# DLMF definitions throughout the chapters and their Lean counterparts

This expanded inventory retains every entry of [DEFINITIONS.md](DEFINITIONS.md)
and adds mathematical definitions under other headings, in DLMF order of first
appearance. The sources are the live NIST DLMF 1.2.8 section pages cached on
2026-10-29. Each entry distinguishes actual Lean definitions, aliases and
representation theorems; domains, normalizations and branch differences matter.
Infinite operations and chosen continuations are totalized in Lean, and a value
outside its intended domain is not thereby a DLMF analytic continuation.

The earlier heading-based scan covered 872 section pages, 102 pages with 111
matching headings, and 267 grouped entries. Those entries are preserved below;
the expanded full-content review covers all 872 sections in all 36 chapters, including their prose, displayed formulas and mathematical table definitions. Its 1,153 correspondence groups comprise the 267 retained groups and 886 additions after related constructions were consolidated. A group may contain several mathematical definitions and several Lean realizations. Chapter 3 and
application/computation sections are included descriptively: numerical methods
or decimal tables are not being acquired as Lean code. Auxiliary coefficients,
coordinate changes, equations and exact limiting notions are included when they
introduce mathematical objects; identities alone are not additional definitions.

## Chapter 1 — Algebraic and analytic methods

Expanded review: all 18 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§1.1–1.18 checked; matching headings are the square-matrix
paragraph in §1.2(vi), §1.8(i), §1.15(i), §1.15(iv), and §1.17(iv).

### §1.1 Special Notation

- **Scalar, vector, matrix and square-integrable-function notation**, [DLMF 1.1](https://dlmf.nist.gov/1.1):
  Real and complex scalars are `ℝ`, `ℂ`; finite vectors are functions `Fin n → 𝕜`, and matrices are `Matrix (Fin m) (Fin n) 𝕜`. The Hilbert-space version of DLMF’s square-integrable functions is `MeasureTheory.Lp ℂ 2 μ`, which identifies functions equal almost everywhere; `MeasureTheory.MemLp f 2 μ` is the corresponding predicate before quotienting. Distribution/test-function notation is developed in §1.16 below.

### §1.2 Elementary Algebra

- **Natural and complex binomial coefficients**, [DLMF 1.2.E1](https://dlmf.nist.gov/1.2.E1):
  `Nat.choose` ([source](.lake/packages/mathlib/Mathlib/Data/Nat/Choose/Basic.lean#L50)), `Ring.choose` ([source](.lake/packages/mathlib/Mathlib/RingTheory/Binomial.lean#L383)). The latter implements the falling-factorial polynomial divided by k!, matching 1.2.6 over ℂ; the natural definition includes k>n as zero.

- **Arithmetic and geometric progression terms**, [DLMF 1.2.E10](https://dlmf.nist.gov/1.2.E10):
  The terms are the expressions a+j d and a x^j, with last arithmetic term ℓ=a+(n−1)d. Their displayed sums are theorems; no separate local progression type is needed.

- **Partial-fraction coefficients Aⱼ, Bⱼ and numerator polynomials**, [DLMF 1.2.E13](https://dlmf.nist.gov/1.2.E13):
  The coefficients of 1.2.13 and 1.2.15 are the displayed evaluations/products and iterated derivatives divided by factorials. Local partial-fraction theorems use these expressions directly; no independently named coefficient functions are defined. The fⱼ of 1.2.16 are existential numerator polynomials, not selected global functions.

- **Arithmetic, geometric and harmonic means**, [DLMF 1.2.E17](https://dlmf.nist.gov/1.2.E17):
  `DLMF.AlgebraicAnalytic.arithmeticMean` ([source](DLMF/AlgebraicAnalytic/Algebra/Basic.lean#L39)), `DLMF.AlgebraicAnalytic.geometricMean` ([source](DLMF/AlgebraicAnalytic/Algebra/Basic.lean#L45)), `DLMF.AlgebraicAnalytic.harmonicMean` ([source](DLMF/AlgebraicAnalytic/Algebra/Basic.lean#L51)). Positive inputs and a nonempty finite family are the intended DLMF domains; division and real roots are totalized otherwise.

- **Weighted power mean and zero-input convention**, [DLMF 1.2.E20](https://dlmf.nist.gov/1.2.E20):
  `DLMF.AlgebraicAnalytic.weightedPowerMean` ([source](DLMF/AlgebraicAnalytic/Algebra/Basic.lean#L57)). It retains the special value zero when r<0 and an input vanishes. At r=0 Lean additionally supplies the weighted geometric mean; DLMF defines only the limiting value, not M(0). Weights being positive and summing to one remain hypotheses.

- **Matrices, transpose, conjugate transpose, matrix product and vectors**, [DLMF 1.2.E27](https://dlmf.nist.gov/1.2.E27):
  `Matrix.transpose` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean#L176)), `Matrix.conjTranspose` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/ConjTranspose.lean#L43)), `Matrix.toLin'` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/ToLin.lean#L386)). Entrywise conjugation is `Matrix.map`; addition, scalar multiplication and matrix multiplication use the standard matrix instances. Rectangular dimensions are encoded by the index types. A column or row vector is a function with the corresponding singleton matrix index.

- **Scalar product, orthogonality and normalization**, [DLMF 1.2.E40](https://dlmf.nist.gov/1.2.E40):
  Mathlib’s complex inner product is conjugate-linear in its first input; DLMF 1.2.40 is linear in its first input, so the correspondence is `⟪v,u⟫` for DLMF ⟨u,v⟩. Orthogonality is vanishing of that inner product; normalization is norm one. `Orthonormal` ([source](.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean#L51)) describes an orthonormal family.

- **Finite ℓᵖ, Euclidean, ℓ¹ and supremum norms**, [DLMF 1.2.E45](https://dlmf.nist.gov/1.2.E45):
  `PiLp` ([source](.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean#L87)), `EuclideanSpace` ([source](.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean#L114)). `PiLp p (fun _ : Fin n => 𝕜)` supplies the finite p-norm; `EuclideanSpace 𝕜 (Fin n)` is p=2. The ordinary finite-function norm is the supremum norm, so it must not silently replace the DLMF Euclidean convention.

- **Identity, diagonal, symmetric, Hermitian, tridiagonal and triangular matrices**, [DLMF 1.2.E53](https://dlmf.nist.gov/1.2.E53):
  `Matrix.IsSymm` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Symmetric.lean#L33)), `Matrix.IsHermitian` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Hermitian.lean#L45)), `DLMF.AlgebraicAnalytic.IsTridiagonal` ([source](DLMF/AlgebraicAnalytic/Algebra/Basic.lean#L71)), `Matrix.IsUpperTriangular` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Block.lean#L66)). Identity and diagonal matrices are `1` and `Matrix.diagonal`; lower triangularity is upper triangularity after transposition. The local tridiagonal predicate uses integer distances between `Fin n` indices.

<!-- retained entry 1 -->
- **Determinant**, [1.2.58–59](https://dlmf.nist.gov/1.2.E59): Mathlib
  `Matrix.det`, defined by the signed permutation sum in
  [Determinant/Basic](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean#L63).
  The permutations and their signs are `Equiv.Perm` and `Equiv.Perm.sign`.

<!-- retained entry 2 -->
- **Inverse; singular and nonsingular matrices**, [1.2.60 and adjacent prose](https://dlmf.nist.gov/1.2#Px12):
  Mathlib's matrix inverse `A⁻¹` in
  [NonsingularInverse](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean#L150),
  and `IsUnit A` for invertibility. Over a field, singularity is `A.det = 0`;
  Lean totalizes the inverse at singular matrices.

<!-- retained entry 3 -->
- **Trace**, [1.2.62](https://dlmf.nist.gov/1.2.E62): Mathlib `Matrix.trace`
  in [Trace](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Trace.lean#L43).

<!-- retained entry 4 -->
- **Commuting matrices and commutator**, [1.2.66 and preceding prose](https://dlmf.nist.gov/1.2.E66):
  `Commute A B` and the ring Lie bracket `⁅A, B⁆ = A * B - B * A`.
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean#L203)
  records the upstream bracket identification.

<!-- retained entry 5 -->
- **Euclidean operator norm**, [1.2.67](https://dlmf.nist.gov/1.2.E67):
  Mathlib's scoped `Matrix.Norms.L2Operator` instance and the norm of the corresponding
  continuous linear map. This requires the Euclidean operator norm, not an
  arbitrary matrix norm; see the explicit use in
  [Matrices](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L212).

<!-- retained entry 6 -->
- **Eigenvalue and eigenvector**, [1.2.70–72](https://dlmf.nist.gov/1.2.E70):
  `Module.End.HasEigenvalue` and `Module.End.HasEigenvector`, applied to the
  matrix linear map, in
  [Eigenspace/Basic](.lake/packages/mathlib/Mathlib/LinearAlgebra/Eigenspace/Basic.lean#L435).

<!-- retained entry 7 -->
- **Linear independence, non-defective/defective matrices, and eigenvalue
  multiplicity**, [prose surrounding 1.2.73](https://dlmf.nist.gov/1.2.E73):
  `LinearIndependent` expresses the eigenvector condition; local statements use
  an invertible matrix of eigenvectors and a diagonal matrix in
  [Matrices](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L239).
  There is no separate local `NonDefective` predicate. Repeated diagonal
  entries are counted by their finite index set; algebraic multiplicity can
  instead be expressed using the characteristic polynomial's root multiplicity.

<!-- retained entry 8 -->
- **Matrix exponential and exponential of the trace**, [1.2.76–77](https://dlmf.nist.gov/1.2.E76):
  Mathlib `NormedSpace.exp`, applied to matrices, and `Complex.exp A.trace`.
  There is no separate local `etr` wrapper here.

### §1.3 Determinants, Linear Operators, and Spectral Expansions

- **Minor and cofactor**, [DLMF 1.3.E3](https://dlmf.nist.gov/1.3.E3):
  Delete the selected row/column using `Matrix.submatrix` and take `Matrix.det`; multiply by (−1)^(j+k) for the cofactor. Mathlib’s adjugate packages these coefficients. These are actual determinant expressions; no separate local minor or cofactor function is introduced.

- **Alternant**, [DLMF 1.3.ii](https://dlmf.nist.gov/1.3.ii):
  A determinant which changes sign when two variables are interchanged; the displayed evaluation matrices 1.3.11–12 are `Matrix.det (fun j k => f k (x j))` and its two-variable analogue. The alternating-map API supplies the general notion, without a local `Alternant` structure.

- **Vandermonde, Cauchy, circulant and Krattenthaler matrices**, [DLMF 1.3.E13](https://dlmf.nist.gov/1.3.E13):
  `Matrix.vandermonde` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Vandermonde.lean#L85)), `Matrix.circulant` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Circulant.lean#L51)). Cauchy’s matrix is the explicit reciprocal-difference matrix in 1.3.14; Krattenthaler’s tⱼₖ in 1.3.16 is a finite product. Their determinant evaluations are bridges, not additional definitions of these matrices.

- **Finite truncation, convergent infinite determinant and Hill type**, [DLMF 1.3.E18](https://dlmf.nist.gov/1.3.E18):
  `DLMF.AlgebraicAnalytic.truncDet` ([source](DLMF/AlgebraicAnalytic/Algebra/Basic.lean#L79)), `DLMF.AlgebraicAnalytic.HasInfiniteDet` ([source](DLMF/AlgebraicAnalytic/Algebra/Basic.lean#L86)), `DLMF.AlgebraicAnalytic.IsHillType` ([source](DLMF/AlgebraicAnalytic/Algebra/Basic.lean#L93)). Truncations range over −n,…,n. The infinite determinant is a convergence predicate, not a chosen limit-valued function; Hill type is absolute summability of the deviation from the identity over ℤ×ℤ.

- **Adjoint, self-adjoint/unitary/orthogonal operators and orthonormal expansion**, [DLMF 1.3.iv](https://dlmf.nist.gov/1.3.iv):
  For finite Euclidean spaces the adjoint is the conjugate transpose; `IsSelfAdjoint` and `Matrix.IsHermitian` express self-adjointness, and `Matrix.unitaryGroup`/`Matrix.orthogonalGroup` express the basis transformations. Expansion coefficients are inner-product expressions, with the argument reversal required by §1.2.40. The spectrum/eigenvalue relation and Parseval identity are theorems.

### §1.4 Calculus of One Variable

- **Monotone, strictly monotone and antitone functions**, [DLMF 1.4.i](https://dlmf.nist.gov/1.4.i):
  `MonotoneOn` ([source](.lake/packages/mathlib/Mathlib/Order/Monotone/Defs.lean#L74)), `StrictMonoOn` ([source](.lake/packages/mathlib/Mathlib/Order/Monotone/Defs.lean#L99)) and the corresponding `AntitoneOn`, `StrictAntiOn` predicates. DLMF “increasing” is the strict convention; “nondecreasing” is Mathlib monotonicity.

- **One-sided continuity, continuity on intervals and removable/simple discontinuities**, [DLMF 1.4.E1](https://dlmf.nist.gov/1.4.E1):
  `ContinuousWithinAt` ([source](.lake/packages/mathlib/Mathlib/Topology/Defs/Filter.lean#L186)), `DLMF.AlgebraicAnalytic.IsSimpleDiscontinuity` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L48)), `DLMF.AlgebraicAnalytic.IsPiecewiseContinuousOn` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L54)). Left/right continuity use `Iic c`/`Ici c` neighborhood filters. Removability is a common finite punctured limit; no selected value is forced at the omitted point. The local piecewise predicate permits finite removable as well as jump discontinuities.

- **Derivative, higher derivatives and Cⁿ/C∞ regularity**, [DLMF 1.4.E4](https://dlmf.nist.gov/1.4.E4):
  `HasDerivAt` ([source](.lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L131)), `iteratedDeriv` ([source](.lake/packages/mathlib/Mathlib/Analysis/Calculus/IteratedDeriv/Defs.lean#L55)), `ContDiffOn` ([source](.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean#L471)). `deriv` is a totalized derivative value; `HasDerivAt`/`DifferentiableAt` assert that it is a derivative. `ContDiffOn ℝ n` retains the within-domain formulation needed at interval endpoints.

- **Local/global extrema and indefinite primitive**, [DLMF 1.4.Px3.p1](https://dlmf.nist.gov/1.4#Px3.p1):
  Local extrema are `IsLocalMax`, `IsLocalMin`, and their within-set forms; global extrema on a set are `IsMaxOn`, `IsMinOn`. An indefinite integral is represented by `HasDerivAt F (f x) x` on the domain, with the additive constant quantified, rather than a canonical global antiderivative.

- **Riemann, improper, Stieltjes and Lebesgue integrals**, [DLMF 1.4.E18](https://dlmf.nist.gov/1.4.E18):
  Mathlib’s `intervalIntegral` is an oriented Bochner interval integral. Its agreement with Riemann sums requires integrability hypotheses; it does not itself define conditionally convergent improper integrals. The latter are limits of interval integrals as in 1.4.22–23. `StieltjesFunction.measure` supplies the Lebesgue–Stieltjes measure; `MeasureTheory.integral` integrates against it. See [Stieltjes](.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Stieltjes.lean).

- **Absolutely continuous measures, densities, atomic masses and mixed measures**, [DLMF 1.4.E23_1](https://dlmf.nist.gov/1.4.E23_1):
  A density w gives `MeasureTheory.Measure.withDensity`; the cumulative integral realizes 1.4.23_1. Absolute continuity is the measure relation `μ ≪ ν`, with a Radon–Nikodym derivative supplying a density under its hypotheses. Atomic masses are scalar multiples of `MeasureTheory.Measure.dirac`, and sums with a density represent 1.4.23_3. An atom here is a point mass, not an ordinary nonzero-valued density at a point.

- **Cauchy principal value at an interior pole and symmetric infinity**, [DLMF 1.4.E24](https://dlmf.nist.gov/1.4.E24):
  `DLMF.AlgebraicAnalytic.HasCauchyPrincipalValue` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L72)), `DLMF.AlgebraicAnalytic.HasPrincipalValueAtInfinity` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L82)). Both predicates retain existence of each truncated integral and convergence of the symmetric limit. An ordinary totalized integral is not a substitute for these principal values.

- **Square integrability and total variation**, [DLMF 1.4.E32](https://dlmf.nist.gov/1.4.E32):
  `MeasureTheory.MemLp` ([source](.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean#L154)), `eVariationOn` ([source](.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/BoundedVariation.lean#L61)), `BoundedVariationOn` ([source](.lake/packages/mathlib/Mathlib/Topology/EMetricSpace/BoundedVariation.lean#L66)). p=2 gives square integrability. The standard extended variation is nonnegative and unoriented on a set; DLMF additionally extends its derivative-integral notation to reversed/infinite endpoints in 1.4.34, which must be compared with the corresponding interval integral, not identified blindly with set variation.

- **Taylor polynomial and remainder**, [DLMF 1.4.E35](https://dlmf.nist.gov/1.4.E35):
  Mathlib `taylorWithinEval`/`taylorWithin` construct Taylor jets; the remainder is the difference between f and its finite Taylor sum, with Lagrange or integral characterization 1.4.36–37. No selected mean-value point c is defined. See [Taylor](.lake/packages/mathlib/Mathlib/Analysis/Calculus/Taylor.lean).

- **Convex function**, [DLMF 1.4.E38](https://dlmf.nist.gov/1.4.E38):
  `ConvexOn` ([source](.lake/packages/mathlib/Mathlib/Analysis/Convex/Function.lean#L54)). The ambient scalars are ℝ, and the interval is part of the predicate; derivative criteria are equivalence theorems under the stated regularity assumptions.

### §1.5 Calculus of Two or More Variables

- **Joint continuity, separate piecewise continuity and partial/mixed derivatives**, [DLMF 1.5.E1](https://dlmf.nist.gov/1.5.E1):
  `DLMF.AlgebraicAnalytic.IsPiecewiseContinuousOnProd` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L63)), `DLMF.AlgebraicAnalytic.partialDeriv` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L91)). Joint continuity is `ContinuousAt` on the product space, stronger than separate continuity; the local piecewise predicate follows DLMF’s separate-variable wording. Mixed derivatives iterate section derivatives. Fréchet differentiability and `ContDiffOn` give the corresponding coordinate-independent regularity under the usual hypotheses.

- **Polar, cylindrical and spherical coordinate maps**, [DLMF 1.5.E10](https://dlmf.nist.gov/1.5.E10):
  `DLMF.AlgebraicAnalytic.cylindricalCoord` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L112)), `DLMF.AlgebraicAnalytic.sphericalCoord` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L118)). Polar coordinates are the first two components (r cos φ,r sin φ). The spherical map uses the physicists’ convention: θ is polar and φ azimuthal. Parameter ranges are hypotheses, not restrictions on the maps; inverse coordinates need singular-axis and periodic-angle conventions.

- **Scalar Laplacian in two and three dimensions**, [DLMF 1.5.E13](https://dlmf.nist.gov/1.5.E13):
  The Cartesian two-variable Laplacian is the sum of the two repeated section derivatives; the three-variable version is `DLMF.AlgebraicAnalytic.laplacian` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L161)). The polar/cylindrical/spherical expressions 1.5.13, 1.5.15, 1.5.17 are coordinate-change identities, not independent functions, and require avoiding coordinate singularities.

- **Multivariable Taylor remainder and Hessian definiteness**, [DLMF 1.5.E18](https://dlmf.nist.gov/1.5.E18):
  The remainder is the function minus its finite directional-derivative Taylor polynomial. Its little-o condition is a filter statement at the basepoint. The quadratic term defines the Hessian quadratic form; `QuadraticForm.PosDef` and matrix positive/negative definiteness express the extremum tests. No canonical intermediate point or remainder coefficient is selected.

- **Uniform convergence of an improper integral**, [DLMF 1.5.E23](https://dlmf.nist.gov/1.5.E23):
  The tail bound is uniform in x∈[a,b], with its cutoff independent of x. It can be expressed using `TendstoUniformlyOn` for truncated integrals, or a product-filter limit. This differs from pointwise existence of each improper integral; there is no special local definition tied only to 1.5.23.

- **Double/triple integrals, zero extension, repeated integrals and domains**, [DLMF 1.5.E27](https://dlmf.nist.gov/1.5.E27):
  Use product measure and `MeasureTheory.integral`; f* in 1.5.28 is `Set.indicator`. Iterated integrals are repeated applications of the one-dimensional integral, with Fubini/Tonelli hypotheses retained. DLMF’s unbounded or singular integrals can instead be improper limits; ordinary totalized product integrals represent the absolutely integrable case, not every conditional iterated limit.

- **Two- and three-dimensional Jacobian determinants**, [DLMF 1.5.E38](https://dlmf.nist.gov/1.5.E38):
  `DLMF.AlgebraicAnalytic.jacobianDet2` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L98)), `DLMF.AlgebraicAnalytic.jacobianDet3` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L105)). These use determinants of section-derivative matrices. The general counterpart is the determinant of the Fréchet derivative. Absolute Jacobians in integration and signed Jacobians as coordinate maps must be distinguished.

### §1.6 Vectors and Vector-Valued Functions

- **Dot product, Euclidean magnitude, vector angle and unit basis**, [DLMF 1.6.E2](https://dlmf.nist.gov/1.6.E2):
  `DLMF.AlgebraicAnalytic.vecNorm` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L128)). `dotProduct` (notation ⬝ᵥ) is the finite dot product; basis vectors are coordinate unit functions. Mathlib `InnerProductGeometry.angle` gives an angle on an inner-product space, with its own totalization when a vector vanishes. The ordinary norm of `Fin 3 → ℝ` is the supremum norm, so the explicit Euclidean magnitude is significant.

- **Cross product, scalar triple product and oriented volume**, [DLMF 1.6.E9](https://dlmf.nist.gov/1.6.E9):
  Mathlib’s `crossProduct` (notation ⨯₃) is the coordinate cross product on `Fin 3 → ℝ`; the scalar triple product is the dot-product expression a·(b×c). Their norm and absolute value give parallelogram area and parallelepiped volume. See [CrossProduct](.lake/packages/mathlib/Mathlib/LinearAlgebra/CrossProduct.lean).

- **Einstein index convention and Levi-Civita symbol**, [DLMF 1.6.E12](https://dlmf.nist.gov/1.6.E12):
  `DLMF.AlgebraicAnalytic.leviCivita` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L134)). The indices are `Fin 3`, zero-based internally; the closed integer product evaluates to the permutation sign or zero for repeats. Repeated-index summation in Lean is an explicit finite sum, not implicit elaborator notation.

- **Gradient, divergence, curl, scalar and vector Laplacians**, [DLMF 1.6.E19](https://dlmf.nist.gov/1.6.E19):
  `DLMF.AlgebraicAnalytic.grad` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L143)), `DLMF.AlgebraicAnalytic.divergence` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L149)), `DLMF.AlgebraicAnalytic.curl` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L154)), `DLMF.AlgebraicAnalytic.laplacian` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L161)), `DLMF.AlgebraicAnalytic.vectorLaplacian` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L167)). These are actual coordinate definitions from `partialDeriv`; del is their differential-operator notation, not an additional independent vector value.

- **Path derivative, length, scalar path integral and vector line integral**, [DLMF 1.6.E35](https://dlmf.nist.gov/1.6.E35):
  `DLMF.AlgebraicAnalytic.pathLength` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L174)), `DLMF.AlgebraicAnalytic.pathIntegral` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L180)), `DLMF.AlgebraicAnalytic.lineIntegral` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L185)). The derivative is `deriv c`; length/path integral use its Euclidean magnitude, while the line integral uses a dot product and changes sign under orientation reversal.

- **Simple closed path, reparametrization and orientation**, [DLMF 1.6.iv.p3](https://dlmf.nist.gov/1.6#iv.p3):
  `DLMF.AlgebraicAnalytic.IsSimpleClosedPath` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L190)). This predicate states endpoint equality and injectivity on [a,b), with a<b; continuity/differentiability are separate hypotheses. A reparametrization is composition with a monotone differentiable map and the specified endpoint correspondence; no distinct local reparametrization structure is selected.

- **Parametrized surfaces, tangent vectors, smoothness and surface area**, [DLMF 1.6.E45](https://dlmf.nist.gov/1.6.E45):
  `DLMF.AlgebraicAnalytic.tangentU` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L198)), `DLMF.AlgebraicAnalytic.tangentV` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L204)), `DLMF.AlgebraicAnalytic.IsSmoothSurfaceAt` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L209)), `DLMF.AlgebraicAnalytic.surfaceArea` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L214)). The parametrization itself is a map ℝ×ℝ→ℝ³. Smoothness here means nonvanishing cross product at a point, rather than unrestricted C∞ regularity of the parametrization.

- **Scalar surface integral, flux, normal derivative and outward orientation**, [DLMF 1.6.E54](https://dlmf.nist.gov/1.6.E54):
  `DLMF.AlgebraicAnalytic.surfaceIntegral` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L219)), `DLMF.AlgebraicAnalytic.fluxIntegral` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L224)), `DLMF.AlgebraicAnalytic.HasPiecewiseSmoothBoundary` ([source](DLMF/AlgebraicAnalytic/Calculus/Basic.lean#L230)). Scalar surface measure uses the magnitude of Tᵤ×Tᵥ; flux uses the oriented vector. The normal derivative is ∇g·n. The boundary structure records smooth parameter patches and an outward-pointing condition; it is more data than the bare assertion that a set is orientable.

### §1.7 Inequalities

- **Hölder conjugate exponents**, [DLMF 1.7.E2](https://dlmf.nist.gov/1.7.E2):
  `Real.HolderConjugate` ([source](.lake/packages/mathlib/Mathlib/Basic/Real/ConjExponents.lean#L60)) expresses p>1 and 1/p+1/q=1. The remaining sections apply the means and integral norms already defined; Cauchy–Schwarz, Hölder, Minkowski and Jensen are inequality theorems, not additional definition objects.

### §1.8 Fourier Series

<!-- retained entry 9 -->
- **Fourier series and trigonometric Fourier coefficients**, [1.8.1–2](https://dlmf.nist.gov/1.8.E2):
  `DLMF.AlgebraicAnalytic.fourierCosCoeff` and `fourierSinCoeff` in
  [Fourier/Defs](DLMF/AlgebraicAnalytic/Fourier/Basic.lean#L42).
  They accept complex-valued functions of a real argument and use DLMF's
  `1/π` normalization; the constant term is `a₀/2`.

<!-- retained entry 10 -->
- **Exponential Fourier coefficients**, [1.8.3–4](https://dlmf.nist.gov/1.8.E4):
  `DLMF.AlgebraicAnalytic.fourierExpCoeff` in
  [Fourier/Defs](DLMF/AlgebraicAnalytic/Fourier/Basic.lean#L49).
  Mathlib `fourierCoeffOn` is another integral construction; the bridge
  `fourierExpCoeff_eq_fourierCoeffOn` accounts for the interval and period.
  Fourier-series sums are expressions built from these coefficients, not
  additional definitions in this file.

<!-- retained entry 11 -->
- **Lebesgue constants**, [1.8.8](https://dlmf.nist.gov/1.8.E8):
  `DLMF.AlgebraicAnalytic.lebesgueConstant` in
  [Fourier/Defs](DLMF/AlgebraicAnalytic/Fourier/Basic.lean#L55).

- **Left and right derivatives and the midpoint jump value**, [DLMF 1.8.ii](https://dlmf.nist.gov/1.8.ii):
  One-sided derivatives are `HasDerivWithinAt` on the left/right half-lines. The Fourier limit at a jump is the expression (f(x−)+f(x+))/2, using the existing one-sided limits. No additional named local function is defined by 1.8.11.

### §1.9 Calculus of a Complex Variable

- **Complex numbers, real/imaginary parts, conjugation, modulus and phase**, [DLMF 1.9.E1](https://dlmf.nist.gov/1.9.E1):
  Mathlib `Complex.re`, `Complex.im`, conjugation and the complex norm implement the Cartesian definitions. `DLMF.AlgebraicAnalytic.IsPhase` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L52)) retains all phases. `Complex.arg` chooses −π<arg≤π; DLMF also permits both banks ±π on the negative axis, so its two-valued principal phase is not literally that single-valued function. The phase at zero is undefined by DLMF, whereas the local predicate permits every value.

- **Neighborhood, open/closed set, accumulation point, domain, closure, boundary and interior**, [DLMF 1.9.ii](https://dlmf.nist.gov/1.9.ii):
  Use Mathlib `Metric.ball`, `IsOpen`, `IsClosed`, `AccPt`, `closure`, `frontier`, `interior`. A DLMF domain is open and connected (equivalently polygonally connected in ℂ); `IsConnected` includes nonemptiness. Continuity on a region with boundary is `ContinuousOn`, hence uses within-set neighborhoods. A “closed domain” in this prose means its closure, not the standard open-domain convention.

- **Complex derivative, holomorphic/entire function and harmonic function**, [DLMF 1.9.E24](https://dlmf.nist.gov/1.9.E24):
  `HasDerivAt`/`DifferentiableAt ℂ` give the complex derivative. `AnalyticAt ℂ`, `AnalyticOnNhd ℂ` describe holomorphy; for open domains these agree with complex differentiability on the domain. Entire means differentiable everywhere over ℂ. Harmonicity is the real Laplace equation together with the required second-order regularity; use Mathlib’s harmonic-function API, not the equation with totalized derivatives alone.

- **Arc, contour, simple closed contour and its orientation**, [DLMF 1.9.iii](https://dlmf.nist.gov/1.9.iii):
  `DLMF.AlgebraicAnalytic.IsSimpleClosedContour` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L149)), `DLMF.AlgebraicAnalytic.contourInterior` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L163)), `DLMF.AlgebraicAnalytic.contourExterior` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L169)), `DLMF.AlgebraicAnalytic.IsPositivelyOriented` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L175)). The contour predicate uses `TauCeti.Contour.IsPiecewiseC1On`; interiors/exteriors use its filled hull. Positive orientation is winding number one on the interior. A path with no multiple points is an injectivity condition, with endpoints identified only in the closed case.

- **Contour integral and winding number**, [DLMF 1.9.E28](https://dlmf.nist.gov/1.9.E28):
  `DLMF.AlgebraicAnalytic.contourIntegral` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L156)) is the parameter integral γ′(t)f(γ(t)); the underlying general API is `TauCeti.Contour`. Its `windingNumber` realizes 1.9.32. Improper contours require truncation limits; ordinary Bochner totalization is not a convergence claim.

- **Poisson disk extension**, [DLMF 1.9.E34](https://dlmf.nist.gov/1.9.E34):
  The displayed integral defines a harmonic extension of boundary data. The unit-circle kernel is `DLMF.AlgebraicAnalytic.abelPoissonKernel`, and the corresponding normalized extension is `abelMean`, in [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L96); radius-R data are obtained by scaling. These are the same mathematical construction in disk/Fourier normalizations, not an additional arbitrary-radius selected function.

- **Extended complex plane and analyticity/derivative at infinity**, [DLMF 1.9.E35](https://dlmf.nist.gov/1.9.E35):
  `DLMF.AlgebraicAnalytic.extAdd` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L62)), `DLMF.AlgebraicAnalytic.extMul` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L69)), `DLMF.AlgebraicAnalytic.extDiv` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L77)), `DLMF.AlgebraicAnalytic.AnalyticAtInfty` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L85)), `DLMF.AlgebraicAnalytic.derivAtInfty` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L92)). The space is `OnePoint ℂ`. Inversion at zero is completed by a supplied value L before taking a derivative. The local extended arithmetic has artificial values for ∞·0 and 0/0, outside the DLMF rules.

- **Conformal map, Möbius map and cross ratio**, [DLMF 1.9.Px22.p1](https://dlmf.nist.gov/1.9#Px22.p1):
  `DLMF.AlgebraicAnalytic.mobius` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L97)), `DLMF.AlgebraicAnalytic.mobiusExt` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L103)), `DLMF.AlgebraicAnalytic.crossRatio` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L110)). The extended Möbius map retains the pole and infinity values; the ordinary quotient is totalized at its pole. The local cross ratio takes four finite complex points only, so the limiting infinity cases remain expressions or a missing extension. Holomorphic maps with nonzero derivative are conformal, expressed through Mathlib `ConformalAt`.

- **Convergent/absolutely convergent series, pointwise and uniform convergence**, [DLMF 1.9.v](https://dlmf.nist.gov/1.9.v):
  Sequence convergence is `Filter.Tendsto`. A conditionally convergent ordered series uses limits of natural partial sums; Mathlib `Summable` is unconditional and over ℂ corresponds to absolute convergence. `TendstoUniformlyOn` and `TendstoLocallyUniformlyOn` distinguish uniform from compact-local convergence. Bilateral ordered convergence requires both half-series, rather than silently identifying it with unconditional summation.

- **Power series, coefficients, convergence disk and radius**, [DLMF 1.9.vi](https://dlmf.nist.gov/1.9.vi):
  `PowerSeries` stores formal coefficients and `FormalMultilinearSeries`/`HasFPowerSeriesOnBall` give the analytic realization and its radius; a native totalized sum alone is not a holomorphic continuation. The Cauchy product coefficients of 1.9.52 are finite convolution sums. The Taylor coefficients are the derivative/factorial expressions 1.9.48.

- **Reciprocal, logarithm and power-series coefficient recursions**, [DLMF 1.9.E54](https://dlmf.nist.gov/1.9.E54):
  `DLMF.AlgebraicAnalytic.recipCoeff` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L118)), `DLMF.AlgebraicAnalytic.logCoeff` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L127)), `DLMF.AlgebraicAnalytic.powCoeff` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L137)). The reciprocal recursion assumes a₀≠0 in its interpretation. Logarithm and complex-power recursions normalize a₀=1 and use the principal branches near zero. Their formal coefficients are defined independently of convergence.

- **Double sequence, rectangular double-series convergence and absolute convergence**, [DLMF 1.9.E64](https://dlmf.nist.gov/1.9.E64):
  A double sequence is a function ℕ×ℕ→ℂ and rectangular convergence is a product-atTop limit. The double-series partial sums are over finite rectangles. This is weaker than `HasSum` over ℕ×ℕ without absolute convergence; the repeated-sum equalities in 1.9.67 are bridge theorems under absolute convergence.

### §1.10 Functions of a Complex Variable

- **Order/multiplicity of an analytic zero and simple zero**, [DLMF 1.10.i](https://dlmf.nist.gov/1.10.i):
  `analyticOrderAt` ([source](.lake/packages/mathlib/Mathlib/Analysis/Analytic/Order.lean#L49)). The value is an extended natural order, including infinite order for a locally zero function. DLMF’s finite multiplicity m≥1 describes a nonzero analytic germ vanishing at the point; m=1 is simple.

- **Analytic continuation on overlapping domains and along a path**, [DLMF 1.10.ii](https://dlmf.nist.gov/1.10.ii):
  An extension is an analytic function agreeing on the overlap; identity-theorem hypotheses determine uniqueness there. Path continuation is a finite chain of such analytic pieces covering successive subarcs. There is no single generic locally selected continuation function in this area; the special-function continuation predicates and choices later in the catalogue implement particular instances. Continuation as a relation is not synonymous with evaluating a totalized series beyond convergence.

- **Laurent series, isolated singularity, pole order and essential singularity**, [DLMF 1.10.E6](https://dlmf.nist.gov/1.10.E6):
  `DLMF.AlgebraicAnalytic.laurentCoeff` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L186)), `meromorphicOrderAt` ([source](.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Order.lean#L50)). Laurent coefficients are circle integrals. The pole order is the negative of a finite meromorphic order; a removable singularity has no negative Laurent part, while an isolated essential singularity has infinitely many negative coefficients. Mathlib meromorphicity excludes essential singularities at a finite point. Classification at infinity applies to f(1/z).

- **Residue at a general isolated singularity and at a pole**, [DLMF 1.10.iii.p5](https://dlmf.nist.gov/1.10#iii.p5):
  `DLMF.AlgebraicAnalytic.residueAt` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L193)). The local definition is a small-radius limit of the −1 Laurent coefficient and includes essential singularities. Its pole restriction agrees with `TauCeti.Contour.residue`; this is a bridge, not equality of the definitions at arbitrary singularities.

- **Logarithmic derivative and continuous change of argument**, [DLMF 1.10.E9](https://dlmf.nist.gov/1.10.E9):
  The logarithmic derivative is Mathlib `logDeriv f`. The change of argument around a closed contour is 2π times the winding number of its image; it uses a continuous lifted argument, not the difference of principal arguments at identical endpoints. Zero and pole counts include multiplicities and are theorem data, not a selected enumeration.

- **Multivalued function, branch, cut and branch point**, [DLMF 1.10.vi](https://dlmf.nist.gov/1.10.vi):
  A multivalued function is represented by a set-valued relation; an analytic branch is a single-valued analytic selection on a cut domain. Branch points are the failure to select a branch on a full punctured neighborhood despite a cut-neighborhood branch. This terminology has no one global local structure. The logarithmic sheet/set-valued objects in Chapter 4 give concrete instances and preserve the two banks; their principal branches must not be substituted for the full relation.

- **Inverse-function and fractional inverse coefficients Fₙ,Gₙ**, [DLMF 1.10.E13](https://dlmf.nist.gov/1.10.E13):
  The coefficients in 1.10.13–17 are residue expressions divided by n; ordinary formal inverse coefficients are supplied by Mathlib power-series compositional inverse theory. Fractional inversion needs a chosen root branch. There is no separately named DLMF coefficient selector here; the actual inverse functions are local inverse/analytic existence data, not globally single-valued inverses.

- **Parameter-dependent contour/real integrals and compact-local uniform convergence**, [DLMF 1.10.E18](https://dlmf.nist.gov/1.10.E18):
  F(z) is the parameter integral in 1.10.18. Uniform convergence on each compact subset is `TendstoLocallyUniformlyOn` for its truncations; the analyticity and differentiation identities are bridge theorems under the stated bounds. This section introduces no additional universal special-function object beyond the integral construction.

- **DLMF convergence of infinite products and absolute/uniform product convergence**, [DLMF 1.10.ix](https://dlmf.nist.gov/1.10.ix):
  `DLMF.AlgebraicAnalytic.ProdConvergesDLMF` ([source](DLMF/AlgebraicAnalytic/Complex/Basic.lean#L204)). It requires a nonzero limit for a tail and allows finitely many zero factors before the tail. Mathlib `Multipliable` is unconditional and permits a zero limit, so the notions are not identical. Uniform convergence refers to the partial-product functions.

- **Weierstrass canonical product and Mittag-Leffler partial-fraction sum**, [DLMF 1.10.E22](https://dlmf.nist.gov/1.10.E22):
  The displayed product P and sum f are exact mathematical constructions using `tprod`/`tsum` on their convergence domains. The local results use their explicit expressions rather than independent named functions. The exponential factors and subtraction terms are regularizations, not numerical approximations; omission changes convergence and the represented function.

- **Generating function and coefficient extraction**, [DLMF 1.10.E26](https://dlmf.nist.gov/1.10.E26):
  The formal counterpart is a `PowerSeries` with coefficient functions pₙ(x); the analytic realization is a convergent sum, and the circle integral is coefficient extraction. The ultraspherical example defines its generating function by the principal power (1−2xz+z²)^(−λ); it is an expression built from the polynomial family recorded under Chapter 18, not a second ultraspherical definition.

### §1.11 Zeros of Polynomials

- **Horner and extended-Horner coefficient sequences**, [DLMF 1.11.E3](https://dlmf.nist.gov/1.11.E3):
  `DLMF.AlgebraicAnalytic.hornerB` ([source](DLMF/AlgebraicAnalytic/Polynomials/Basic.lean#L38)), `DLMF.AlgebraicAnalytic.hornerC` ([source](DLMF/AlgebraicAnalytic/Polynomials/Basic.lean#L46)). They are defined from polynomial division by X−α; the recurrences and evaluation/derivative equalities are bridges. Thus these are exact polynomial constructions, not an acquired floating-point algorithm.

- **Monic polynomial, zeros with multiplicity, reciprocal polynomial and discriminant**, [DLMF 1.11.ii](https://dlmf.nist.gov/1.11.ii):
  Mathlib `Polynomial.Monic`, `Polynomial.roots`, `Polynomial.rootMultiplicity`, `Polynomial.reverse`, `Polynomial.discr` supply these objects. A reciprocal polynomial with a supplied degree may need explicit padding/reversal conventions if the constant term vanishes. Elementary symmetric root functions are finite products/sums, with Vieta’s formulas as bridges.

- **Quadratic/cubic/quartic reduced coefficients, discriminants and radicals**, [DLMF 1.11.E11](https://dlmf.nist.gov/1.11.E11):
  The p,q,r reductions of 1.11.12–17, Cardano quantities A,B and cube root ρ, and constrained square roots of 1.11.19–20 are explicit algebraic expressions. Mathlib `Cubic` and `Polynomial.discr` encode the polynomials/discriminants; no independently selected Cardano radical family is defined locally. The correlated square-root sign condition in the quartic formula must be retained.

- **DLMF quartic resolvent cubic**, [DLMF 1.11.E18](https://dlmf.nist.gov/1.11.E18):
  `DLMF.AlgebraicAnalytic.dlmfResolventCubic` ([source](DLMF/AlgebraicAnalytic/Polynomials/Basic.lean#L53)). It is z³−2pz²+(p²−4r)z+q². TauCeti’s `resolventCubic` uses a different normalization, so it is a related object requiring a variable/coefficient conversion, not a direct alias.

- **Roots of unity and roots of a complex constant**, [DLMF 1.11.E21](https://dlmf.nist.gov/1.11.E21):
  Mathlib `rootsOfUnity`, `IsPrimitiveRoot`, and the polynomial root set encode the roots. The listed exponential/polar expressions enumerate them for positive n; the set of n roots is distinct from choosing a principal nth root. The quotient at n=0 is outside the intended formulas.

- **Stable polynomial, Hurwitz matrix and Hurwitz determinants**, [DLMF 1.11.E24](https://dlmf.nist.gov/1.11.E24):
  `DLMF.AlgebraicAnalytic.IsStablePolynomial` ([source](DLMF/AlgebraicAnalytic/Polynomials/Basic.lean#L60)), `DLMF.AlgebraicAnalytic.coeffInt` ([source](DLMF/AlgebraicAnalytic/Polynomials/Basic.lean#L67)), `DLMF.AlgebraicAnalytic.hurwitzMatrix` ([source](DLMF/AlgebraicAnalytic/Polynomials/Basic.lean#L72)), `DLMF.AlgebraicAnalytic.hurwitzDet` ([source](DLMF/AlgebraicAnalytic/Polynomials/Basic.lean#L79)). Coefficients outside the degree range are zero. The stability predicate tests the finite root multiset, so the zero polynomial is vacuously stable; the Hurwitz criterion requires a nonzero leading coefficient.

### §1.12 Continued Fractions

- **Generalized continued fraction, convergent, canonical numerator/denominator and nested tail**, [DLMF 1.12.E1](https://dlmf.nist.gov/1.12.E1):
  `DLMF.AlgebraicAnalytic.contFrac` ([source](DLMF/AlgebraicAnalytic/ContinuedFractions/Basic.lean#L39)), `DLMF.AlgebraicAnalytic.contFracTail` ([source](DLMF/AlgebraicAnalytic/ContinuedFractions/Basic.lean#L46)). The underlying `GenContFract` object has `nums`, `dens`, `convs`, `convs'` and auxiliary initial pair. DLMF a₁ is the first numerator; local `a 0` is unused. Canonical Aₙ/Bₙ and nested division agree only when the relevant denominators do not vanish; totalized complex division does not model ∞.

- **Equivalence and normalization factors for continued fractions**, [DLMF 1.12.ii](https://dlmf.nist.gov/1.12.ii):
  `DLMF.AlgebraicAnalytic.ContFracEquiv` ([source](DLMF/AlgebraicAnalytic/ContinuedFractions/Basic.lean#L58)), `DLMF.AlgebraicAnalytic.contFracUnitFactor` ([source](DLMF/AlgebraicAnalytic/ContinuedFractions/Basic.lean#L64)). Equivalence means equality of all convergents. The dₙ factor recurrence supplies the unit-numerator transformation when its nonvanishing hypotheses hold.

- **Fractional approximant Cₙ(w)**, [DLMF 1.12.E20](https://dlmf.nist.gov/1.12.E20):
  `DLMF.AlgebraicAnalytic.contFracApprox` ([source](DLMF/AlgebraicAnalytic/ContinuedFractions/Basic.lean#L52)). It replaces the final bₙ by bₙ+w in the nested fraction. The extended value at w=∞ is the preceding convergent; no separate infinity-valued approximant function is defined by this ordinary-field object.

- **Contraction, extension, even/odd parts and convergence**, [DLMF 1.12.iv](https://dlmf.nist.gov/1.12.iv):
  `DLMF.AlgebraicAnalytic.IsContraction` ([source](DLMF/AlgebraicAnalytic/ContinuedFractions/Basic.lean#L72)), `DLMF.AlgebraicAnalytic.evenPartA` ([source](DLMF/AlgebraicAnalytic/ContinuedFractions/Basic.lean#L85)), `DLMF.AlgebraicAnalytic.evenPartB` ([source](DLMF/AlgebraicAnalytic/ContinuedFractions/Basic.lean#L94)), `DLMF.AlgebraicAnalytic.oddPartA` ([source](DLMF/AlgebraicAnalytic/ContinuedFractions/Basic.lean#L103)), `DLMF.AlgebraicAnalytic.oddPartB` ([source](DLMF/AlgebraicAnalytic/ContinuedFractions/Basic.lean#L111)), `DLMF.AlgebraicAnalytic.ContFracConverges` ([source](DLMF/AlgebraicAnalytic/ContinuedFractions/Basic.lean#L79)). Contraction is a strictly increasing subsequence of convergents; extension reverses that relation. Even/odd coefficients are the explicit DLMF formulas, and convergence means a finite limit.

### §1.13 Differential Equations

- **Simply connected domain, second-order linear ODE, fundamental pair and Wronskians**, [DLMF 1.13.i](https://dlmf.nist.gov/1.13.i):
  `DLMF.AlgebraicAnalytic.IsLinODE2SolOn` ([source](DLMF/AlgebraicAnalytic/ODE/Basic.lean#L35)), `DLMF.AlgebraicAnalytic.IsFundamentalPair` ([source](DLMF/AlgebraicAnalytic/ODE/Basic.lean#L42)), `DLMF.AlgebraicAnalytic.wronskian` ([source](DLMF/AlgebraicAnalytic/ODE/Basic.lean#L49)), `DLMF.AlgebraicAnalytic.wronskianN` ([source](DLMF/AlgebraicAnalytic/ODE/Basic.lean#L54)). The solution predicate includes genuine derivatives. The source’s simply connected planar domain corresponds to the topological simply-connected condition under its open-domain assumptions. Fundamental solutions with prescribed initial data are existentially characterized, not globally selected by this definitions file.

- **Variation-of-parameters particular solution and transformed ODE coefficients**, [DLMF 1.13.E10](https://dlmf.nist.gov/1.13.E10):
  The particular solution in 1.13.10 is a combination of two primitives divided by their Wronskian. W,F,G in 1.13.12, H in 1.13.15, and η in 1.13.16 are explicit substitutions and coefficient expressions in the local transformation theorems; no additional universal coefficient functions are named. Choice of primitive and nonzero coordinate derivatives remain relevant.

- **Liouville dependent-variable transform and Schwarzian derivative**, [DLMF 1.13.E18](https://dlmf.nist.gov/1.13.E18):
  `DLMF.AlgebraicAnalytic.schwarzian` ([source](DLMF/AlgebraicAnalytic/ODE/Basic.lean#L60)). U=(ζ′)^(1/2)W is the local transformed function expression; the square-root branch and nonvanishing derivative matter. The Schwarzian is z‴/z′−(3/2)(z″/z′)², with totalized division outside its intended domain.

- **Sturm–Liouville equation, unmixed/periodic boundary conditions and eigenvalue**, [DLMF 1.13.E26](https://dlmf.nist.gov/1.13.E26):
  `DLMF.AlgebraicAnalytic.IsSturmLiouvilleSolOn` ([source](DLMF/AlgebraicAnalytic/ODE/Basic.lean#L66)), `DLMF.AlgebraicAnalytic.SLUnmixedBC` ([source](DLMF/AlgebraicAnalytic/ODE/Basic.lean#L73)), `DLMF.AlgebraicAnalytic.SLPeriodicBC` ([source](DLMF/AlgebraicAnalytic/ODE/Basic.lean#L80)), `DLMF.AlgebraicAnalytic.IsRegularSLEigenvalue` ([source](DLMF/AlgebraicAnalytic/ODE/Basic.lean#L85)), `DLMF.AlgebraicAnalytic.IsPeriodicSLEigenvalue` ([source](DLMF/AlgebraicAnalytic/ODE/Basic.lean#L95)). Eigenvalues require a nonzero solution satisfying the specified boundary conditions; p,ρ positivity and nondegenerate boundary coefficients are recorded in the predicates.

- **Liouville normal coordinate, potential and eigenfunction nodes**, [DLMF 1.13.E29](https://dlmf.nist.gov/1.13.E29):
  The coordinate t is the positive-density integral, w=u(pρ)^(1/4), and q̂ is the transformed potential in 1.13.30–31. They are expressions in the Sturm–Liouville transformation statements; no globally selected inverse coordinate is fixed here. Nodes are interior zeros, counted in the relevant eigenfunction theorem rather than by a new universal node-list definition.

### §1.14 Integral Transforms

- **Fourier transform in DLMF and Mathlib normalizations**, [DLMF 1.14.E1](https://dlmf.nist.gov/1.14.E1):
  `DLMF.AlgebraicAnalytic.fourierTransform` ([source](DLMF/AlgebraicAnalytic/Transforms/Basic.lean#L48)). It uses exp(+ixt)/√(2π). Mathlib’s Fourier transform uses exp(−2πitξ); the bridge evaluates the latter at ξ=−x/(2π) and supplies the symmetric factor. The L² extension and distribution transform are different constructions, described in §1.16.

- **Fourier convolution**, [DLMF 1.14.E5](https://dlmf.nist.gov/1.14.E5):
  `DLMF.AlgebraicAnalytic.fourierConvolution` ([source](DLMF/AlgebraicAnalytic/Transforms/Basic.lean#L64)). DLMF includes 1/√(2π); Mathlib `MeasureTheory.convolution` has no such factor. They represent the same convolution after normalization, not a literal alias.

- **Fourier cosine and sine transforms**, [DLMF 1.14.E9](https://dlmf.nist.gov/1.14.E9):
  `DLMF.AlgebraicAnalytic.fourierCosTransform` ([source](DLMF/AlgebraicAnalytic/Transforms/Basic.lean#L54)), `DLMF.AlgebraicAnalytic.fourierSinTransform` ([source](DLMF/AlgebraicAnalytic/Transforms/Basic.lean#L59)). Both use the half-line integral with √(2/π); even/odd extension relates them to the full-line Fourier construction.

- **Laplace transform and exponential-growth class**, [DLMF 1.14.E17](https://dlmf.nist.gov/1.14.E17):
  `DLMF.AlgebraicAnalytic.laplaceTransform` ([source](DLMF/AlgebraicAnalytic/Transforms/Basic.lean#L70)), `DLMF.AlgebraicAnalytic.IsOfExponentialGrowth` ([source](DLMF/AlgebraicAnalytic/Transforms/Basic.lean#L75)). The domain Re s>α follows from the growth bound plus integrability/regularity assumptions. This actual half-line integral is distinct from a theorem giving large-parameter Laplace asymptotics.

- **Exponential translate, delayed input and Laplace moment inputs**, [DLMF 1.14.E21](https://dlmf.nist.gov/1.14.E21):
  The auxiliary inputs are fₐ(t)=e^(at)f(t), fₐ⁺(t)=H(t−a)f(t−a), and fₙ(t)=tⁿf(t), including f₋₁=f(t)/t in 1.14.24. Local theorems use these expressions directly; no extra named function families are defined.

- **Laplace convolution**, [DLMF 1.14.E30](https://dlmf.nist.gov/1.14.E30):
  `DLMF.AlgebraicAnalytic.laplaceConvolution` ([source](DLMF/AlgebraicAnalytic/Transforms/Basic.lean#L81)). It is the oriented finite integral from 0 to t and matches DLMF for t≥0; it differs from normalized full-line Fourier convolution.

- **Mellin transform and its strip of convergence**, [DLMF 1.14.E32](https://dlmf.nist.gov/1.14.E32):
  `mellin` ([source](.lake/packages/mathlib/Mathlib/Analysis/MellinTransform.lean#L91)). This is Mathlib’s native half-line integral with x^(s−1), matching the DLMF normalization. The convergence strip is the set of real exponents for which the weighted input is integrable; it is not a globally selected interval attached to every input.

- **Mellin convolution**, [DLMF 1.14.E39](https://dlmf.nist.gov/1.14.E39):
  `DLMF.AlgebraicAnalytic.mellinConvolution` ([source](DLMF/AlgebraicAnalytic/Transforms/Basic.lean#L86)). The multiplicative measure dy/y is explicit; the product formula for Mellin transforms is a bridge under integrability assumptions.

- **Hilbert transform, truncations and sharp norm constant**, [DLMF 1.14.E41](https://dlmf.nist.gov/1.14.E41):
  `DLMF.AlgebraicAnalytic.hilbertTruncated` ([source](DLMF/AlgebraicAnalytic/Transforms/Basic.lean#L91)), `DLMF.AlgebraicAnalytic.hilbertTransform` ([source](DLMF/AlgebraicAnalytic/Transforms/Basic.lean#L96)). The sign is f(t)/(t−x), and the defining limit removes |t−x|≤ε. The regularized-kernel and antisymmetric-tail forms 1.14.42–43 are theorem representations. Aₚ in 1.14.45 is the displayed tangent/cotangent expression, without another local definition.

- **Stieltjes transform**, [DLMF 1.14.E47](https://dlmf.nist.gov/1.14.E47):
  `DLMF.AlgebraicAnalytic.stieltjesTransform` ([source](DLMF/AlgebraicAnalytic/Transforms/Basic.lean#L103)). It is the actual integral f(t)/(s+t) over t>0. The principal cut is (−∞,0]; boundary jumps and the double-Laplace relation are bridge theorems, not alternative selected transforms.

### §1.15 Summability Methods

<!-- retained entry 12 -->
- **Partial sums**, [1.15.1](https://dlmf.nist.gov/1.15.E1):
  `DLMF.AlgebraicAnalytic.seriesPartialSum` in
  [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L54).

<!-- retained entry 13 -->
- **Abel summability of a series**, [1.15.2–3](https://dlmf.nist.gov/1.15.E3):
  `DLMF.AlgebraicAnalytic.HasAbelSum` in
  [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L59),
  including summability for every real `0 < x < 1` and the limit from below.

<!-- retained entry 14 -->
- **Cesàro summability**, [1.15.4–5](https://dlmf.nist.gov/1.15.E5):
  `cesaroMean` and `HasCesaroSum` in
  [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L66),
  in namespace `DLMF.AlgebraicAnalytic`.

<!-- retained entry 15 -->
- **General Cesàro summability**, [1.15.6–7](https://dlmf.nist.gov/1.15.E7):
  `DLMF.AlgebraicAnalytic.cesaroMeanOfOrder` and `HasCesaroSumOfOrder`
  in [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L75).
  The definition accepts all real orders; DLMF's interpretation assumes `α > -1`.

<!-- retained entry 16 -->
- **Borel summability**, [1.15.8–9](https://dlmf.nist.gov/1.15.E9):
  `DLMF.AlgebraicAnalytic.HasBorelSum` in
  [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L86).
  This is the exponential generating function of the partial sums, not of the
  original terms; convergence for every nonnegative real argument is included.

- **Regular summation method**, [DLMF 1.15.ii](https://dlmf.nist.gov/1.15.ii):
  Regularity is preservation of the ordinary sum by the summation relation. The local Abel/Cesàro/Borel regularity results are implications between the corresponding predicates; no general abstract summation-method structure is introduced.

- **Circle Poisson and Fejér kernels**, [DLMF 1.15.E12](https://dlmf.nist.gov/1.15.E12):
  `DLMF.AlgebraicAnalytic.abelPoissonKernel` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L96)), `DLMF.AlgebraicAnalytic.fejerKernel` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L101)). Their circle means are normalized to one. The quotient definition of `fejerKernel` is totalized to zero at θ∈2πℤ rather than its removable value n+1; this changes no integral but matters for pointwise equality.

- **Fourier Abel mean, symmetric partial sum, Cesàro mean and analytic extension**, [DLMF 1.15.E18](https://dlmf.nist.gov/1.15.E18):
  `DLMF.AlgebraicAnalytic.abelMean` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L126)), `DLMF.AlgebraicAnalytic.fourierPartialSum` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L132)), `DLMF.AlgebraicAnalytic.fourierCesaroMean` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L137)), `DLMF.AlgebraicAnalytic.fourierAnalyticExtension` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L142)). The Abel mean is defined by the normalized Poisson integral, with the r^|n| series as a bridge; the analytic extension is the one-sided positive-frequency series of 1.15.27. Its imaginary part is the conjugate Poisson sum, not a separately named selected harmonic conjugate.

<!-- retained entry 17 -->
- **Abel summability of an integral**, [1.15.29–30](https://dlmf.nist.gov/1.15.E30):
  `DLMF.AlgebraicAnalytic.HasAbelIntegral` in
  [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L151).

<!-- retained entry 18 -->
- **Cesàro summability of an integral**, [1.15.31–32](https://dlmf.nist.gov/1.15.E32):
  `DLMF.AlgebraicAnalytic.HasCesaroIntegral` in
  [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L158).

- **Half-plane Poisson kernel, Fourier Abel mean and Cauchy/Poisson integral**, [DLMF 1.15.E33](https://dlmf.nist.gov/1.15.E33):
  `DLMF.AlgebraicAnalytic.halfPlanePoissonKernel` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L165)), `DLMF.AlgebraicAnalytic.fourierAbelMean` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L170)), `DLMF.AlgebraicAnalytic.poissonCauchyIntegral` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L177)). The kernel is 2y/(x²+y²), with the outer 1/(2π) factor. The conjugate Poisson integral is the imaginary part of the Cauchy integral; the y>0 domain and the DLMF Hilbert-transform sign matter.

- **Line Fejér kernel and Fourier-integral Cesàro mean**, [DLMF 1.15.E41](https://dlmf.nist.gov/1.15.E41):
  `DLMF.AlgebraicAnalytic.fejerKernelLine` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L182)), `DLMF.AlgebraicAnalytic.fourierCesaroMeanIntegral` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L187)). The kernel is (1−cos(Rs))/(πRs²), normalized to integral one for R>0; its removable point value is totalized by the quotient. The mean is the truncated weighted Fourier inverse, with the kernel convolution as a bridge.

- **Riemann–Liouville fractional integrals, shifted/right-sided and Weyl variants**, [DLMF 1.15.E47](https://dlmf.nist.gov/1.15.E47):
  `DLMF.AlgebraicAnalytic.fractionalIntegral` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L196)), `DLMF.AlgebraicAnalytic.riemannLiouvilleIntegralFrom` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L203)), `DLMF.AlgebraicAnalytic.riemannLiouvilleIntegralUpper` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L209)), `DLMF.AlgebraicAnalytic.weylFractionalIntegral` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L215)). These are independent finite/half-line integral definitions, with 1/Γ(α) and the stated nonnegative-real-base principal power. Re α>0 and endpoint/integrability conditions distinguish the variants.

- **Fractional derivative and the selected integer order**, [DLMF 1.15.E51](https://dlmf.nist.gov/1.15.E51):
  `DLMF.AlgebraicAnalytic.fractionalDerivativeOrder` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L222)), `DLMF.AlgebraicAnalytic.fractionalDerivative` ([source](DLMF/AlgebraicAnalytic/Summability/Basic.lean#L226)). The implementation selects n=⌊Re α⌋₊+1 and applies n ordinary derivatives to the order n−α fractional integral. Independence of admissible n and composition identities are additional theorems, not consequences of totalized differentiation.

### §1.16 Distributions

- **Support, test function, test-function convergence, distribution and regular distribution**, [DLMF 1.16.i](https://dlmf.nist.gov/1.16.i):
  Mathlib `tsupport`, `HasCompactSupport`, `TestFunction`, `Distribution` supply the spaces and support notions; distributions are continuous linear maps on the appropriate test-function space. The implementation tests against real test functions and allows complex values. `Distribution.ofFun` constructs a regular distribution from a locally integrable function; a singular distribution means no such representing function, not a function with a point singularity alone.

- **Lebesgue–Stieltjes distribution, smooth multiplication and weak distribution convergence**, [DLMF 1.16.E3_5](https://dlmf.nist.gov/1.16.E3_5):
  `DLMF.AlgebraicAnalytic.stieltjesDistribution` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L66)), `DLMF.AlgebraicAnalytic.smoothMul` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L83)), `DLMF.AlgebraicAnalytic.lineDistrib` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L91)). Stieltjes data are real-valued, nondecreasing and right-continuous, whereas DLMF allows infinite endpoint values. Distribution convergence in 1.16.7 is convergence after pairing with every test function; smooth multiplication is precomposition by multiplication of the test function.

- **Distributional derivatives and shifted Dirac deltas**, [DLMF 1.16.E8](https://dlmf.nist.gov/1.16.E8):
  `DLMF.AlgebraicAnalytic.distribIterDeriv` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L75)). Mathlib `Distribution.delta`, `TemperedDistribution.delta` and the directional distribution derivative supply δₐ and its derivatives. The (−1)^n pairing factor is built into distributional differentiation; these are not derivatives of an ordinary pointwise delta function.

- **Heaviside function and derivative-jump coefficients**, [DLMF 1.16.E13](https://dlmf.nist.gov/1.16.E13):
  `DLMF.AlgebraicAnalytic.heaviside` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L50)), `DLMF.AlgebraicAnalytic.heavisideTempered` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L158)). The point value is H(0)=0. The jump coefficients σₙ of 1.16.17 are differences of the two one-sided derivative limits; they are expressions in the jump-derivative theorem, without an independent selected coefficient family.

- **Positive-part power and logarithm as functions and distributions**, [DLMF 1.16.E19](https://dlmf.nist.gov/1.16.E19):
  `DLMF.AlgebraicAnalytic.xPlusRpow` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L55)), `DLMF.AlgebraicAnalytic.logPlus` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L60)), `DLMF.AlgebraicAnalytic.xPlusDistrib` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L97)). For α>−1 the distribution is regular. Nonintegral α<−1 uses a finite distributional derivative divided by (α+1)ₙ; negative integral α uses derivatives of log₊ and factorial/sign factors. These continuation constructions differ from the ordinary nonintegrable function x₊^α.

- **Schwartz functions, tempered distributions and their weak convergence**, [DLMF 1.16.v](https://dlmf.nist.gov/1.16.v):
  Mathlib `SchwartzMap` and `TemperedDistribution` represent the rapidly decaying smooth test functions and their continuous linear dual. Seminorm bounds control every polynomially weighted derivative; pointwise convergence of pairings is the weak distribution topology. The multivariable versions in §1.16(vi) use finite-dimensional real Euclidean spaces and multi-indices.

- **DLMF Fourier transform on Schwartz space and tempered distributions**, [DLMF 1.16.E29](https://dlmf.nist.gov/1.16.E29):
  `DLMF.AlgebraicAnalytic.dlmfFourierSchwartz` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L130)), `DLMF.AlgebraicAnalytic.dlmfFourierTempered` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L142)). The first is built from Mathlib’s inverse transform, scaling x by 1/(2π) and multiplying by (2π)^(−n/2); the second is its transpose. They are actual constructions with DLMF’s positive exponential sign, not aliases for Mathlib’s convention.

- **Polynomial multiplication and differential operators on test functions and distributions**, [DLMF 1.16.E30](https://dlmf.nist.gov/1.16.E30):
  `DLMF.AlgebraicAnalytic.dlmfD` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L176)), `DLMF.AlgebraicAnalytic.polyOp` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L169)), `DLMF.AlgebraicAnalytic.polyEval` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L189)), `DLMF.AlgebraicAnalytic.polyMul` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L194)), `DLMF.AlgebraicAnalytic.polyDiffOp` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L183)), `DLMF.AlgebraicAnalytic.polyNeg` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L199)), `DLMF.AlgebraicAnalytic.temperedD` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L203)), `DLMF.AlgebraicAnalytic.temperedPolyDiffOp` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L209)), `DLMF.AlgebraicAnalytic.temperedPolyMul` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L215)). The coefficient polynomial is an `MvPolynomial`; Dⱼ=(1/i)∂ⱼ, and P₋ evaluates P at −x. Distribution derivatives act by the signed transpose, preserving the Fourier identities’ sign convention.

- **Sign and bounded-function tempered distributions**, [DLMF 1.16.E44](https://dlmf.nist.gov/1.16.E44):
  `DLMF.AlgebraicAnalytic.boundedTempered` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L148)), `DLMF.AlgebraicAnalytic.signTempered` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L155)). The general construction uses an essentially bounded function’s L∞ class and returns zero if that hypothesis fails. The sign function uses Mathlib `Real.sign`, whose value at zero is zero; the DLMF identity sign=2H−1 is stated away from zero.

### §1.17 Integral and Series Representations of the Dirac Delta

- **Delta sequence, Gaussian profile and test-function restriction**, [DLMF 1.17.E3](https://dlmf.nist.gov/1.17.E3):
  `DLMF.AlgebraicAnalytic.IsDeltaSequence` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L225)), `DLMF.AlgebraicAnalytic.gaussianDeltaSeq` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L234)), `DLMF.AlgebraicAnalytic.normalizedGaussian` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L243)), `DLMF.AlgebraicAnalytic.IsTestFunctionOn` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L238)). The predicate is weak convergence against every smooth compactly supported test function and every translate; the Gaussian sequence has exact √(n/π) normalization. The Fourier/Bessel/Airy/Coulomb integral formulas are representation/completeness theorems for δ, not alternate ordinary delta functions.

- **Periodic Dirichlet delta kernel**, [DLMF 1.17.E20](https://dlmf.nist.gov/1.17.E20):
  `DLMF.AlgebraicAnalytic.dirichletKernel` ([source](DLMF/AlgebraicAnalytic/Distributions/Basic.lean#L246)). This is the finite exponential sum divided by 2π, including its true removable value at multiples of 2π; the quotient is a theorem away from those points. The formal infinite periodic delta series and the Legendre/Laguerre/Hermite/harmonic series are distributional representations, not convergent pointwise definitions of δ.

<!-- retained entry context1.17 -->
[This heading](https://dlmf.nist.gov/1.17.iv) contains bibliographic guidance
about rigorous treatments of the delta representations in earlier subsections;
it introduces no further mathematical definition. The delta distribution itself is defined in §1.16 and is catalogued there.

### §1.18 Linear Second Order Differential Operators and Eigenfunction Expansions

- **Inner-product space, Hilbert space, separability, orthonormal basis and ℓ²**, [DLMF 1.18.E1](https://dlmf.nist.gov/1.18.E1):
  Mathlib `InnerProductSpace ℂ`, `CompleteSpace`, `SeparableSpace`, `Orthonormal`, `HilbertBasis`, and `lp` at p=2 give these objects. DLMF’s inner product is linear in its first variable, opposite to Mathlib’s complex convention. The coefficients are corresponding reversed-argument inner products; completeness means norm convergence of the expansion, not mere pairwise orthogonality.

- **Weighted L² interval space, Fourier coefficients and completeness kernel**, [DLMF 1.18.E11](https://dlmf.nist.gov/1.18.E11):
  `MeasureTheory.Lp ℂ 2 (μ.restrict X)` identifies functions equal μ-almost everywhere, where μ is the Stieltjes/weighted measure. Coefficients are the integrals against conjugate eigenfunctions. K(x,y) in 1.18.18 is the formal sum of rank-one kernels; equality with δ is a distributional completeness relation, not an ordinary pointwise kernel definition.

- **Bounded and densely defined unbounded linear operators, domain, range and adjoint**, [DLMF 1.18.E21](https://dlmf.nist.gov/1.18.E21):
  Mathlib `ContinuousLinearMap` supplies bounded operators, and `LinearPMap` supplies partially defined linear operators and their domains. A bounded operator’s adjoint is `ContinuousLinearMap.adjoint`; densely defined adjoints use the partial-operator API. Unboundedness is failure of an operator-norm bound on the domain; equality of a differential expression with its formal adjoint does not identify their operator domains.

- **Schrödinger differential expression and solution predicate**, [DLMF 1.18.E28](https://dlmf.nist.gov/1.18.E28):
  `DLMF.AlgebraicAnalytic.schrodingerOp` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L50)), `DLMF.AlgebraicAnalytic.IsSchrodingerSolOn` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L159)). The expression −f″+qf on ordinary functions is distinct from a self-adjoint operator on L² with a specified domain and boundary conditions. The solution predicate includes actual differentiability.

- **Eigenfunction coefficient, unitary transform and spectral diagonalization**, [DLMF 1.18.E32](https://dlmf.nist.gov/1.18.E32):
  `DLMF.AlgebraicAnalytic.eigenCoeff` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L212)), `DLMF.AlgebraicAnalytic.IsEigenfunctionTransform` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L218)), `DLMF.AlgebraicAnalytic.IsDiagonalizedBy` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L234)). The transform U is supplied as a unitary equivalence, not chosen from an admitted spectral existence statement. A spectral measure may combine continuous measure and atoms, retaining eigenvalue multiplicities via the required eigenfunction indexing. F(T) is then the conjugated multiplier, under its domain conditions.

- **Normalized sine, cosine, exponential and Hermite eigenfunctions**, [DLMF 1.18.E36](https://dlmf.nist.gov/1.18.E36):
  `DLMF.AlgebraicAnalytic.sinEigenfunction` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L70)), `DLMF.AlgebraicAnalytic.cosEigenfunction` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L74)), `DLMF.AlgebraicAnalytic.expEigenfunction` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L81)), `DLMF.AlgebraicAnalytic.hermiteFunction` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L85)). The cosine zero mode has a different normalization; signed exponential modes encode the multiplicity-two positive periodic eigenvalues. The Hermite construction converts Mathlib’s probabilists’ polynomial to the physicists’ convention and includes the Gaussian L² normalization.

- **Hermite, Bessel and radial Schrödinger operators**, [DLMF 1.18.E41](https://dlmf.nist.gov/1.18.E41):
  `DLMF.AlgebraicAnalytic.hermiteOp` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L56)), `DLMF.AlgebraicAnalytic.besselOp` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L60)), `DLMF.AlgebraicAnalytic.radialSchrodingerOp` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L64)). These are distinct differential expressions with their stated potentials and factors of 1/2. The Bessel and radial singular endpoints require domain/boundary data before they become self-adjoint L² operators.

- **Spectral bands, mixed spectra, almost-Mathieu potential and resonances**, [DLMF 1.18.vii](https://dlmf.nist.gov/1.18.vii):
  Bands are intervals in the continuous spectrum; mixed spectra combine a point part and a continuous part with a spectral measure. The almost-Mathieu cosine potential and complex-dilation parameter in §1.18(viii) are displayed expressions, without selected local operator families. Resonance locations and widths are poles of continued resolvent matrix elements; no local global resonance/width selector is defined.

- **Deficiency spaces and indices, limit-circle/limit-point endpoints**, [DLMF 1.18.ix](https://dlmf.nist.gov/1.18.ix):
  `DLMF.AlgebraicAnalytic.deficiencySubspace` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L144)), `DLMF.AlgebraicAnalytic.deficiencyIndices` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L149)), `DLMF.AlgebraicAnalytic.l2SolutionSpace` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L186)), `DLMF.AlgebraicAnalytic.AllSolutionsL2Left` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L164)), `DLMF.AlgebraicAnalytic.AllSolutionsL2Right` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L168)), `DLMF.AlgebraicAnalytic.AllSolutionsL2Ici` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L173)), `DLMF.AlgebraicAnalytic.IsLimitCircleLeft` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L177)), `DLMF.AlgebraicAnalytic.IsLimitCircleRight` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L182)). The indices are cardinal dimensions at ±i. Limit-circle predicates require all solutions to be square integrable near the endpoint for every spectral parameter; the alternative limit-point case is expressed by negation under the Weyl hypotheses.

- **Symmetric, essentially self-adjoint and self-adjoint operators**, [DLMF 1.18.E68](https://dlmf.nist.gov/1.18.E68):
  `DLMF.AlgebraicAnalytic.IsSymmetricOp` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L101)), `DLMF.AlgebraicAnalytic.IsEssentiallySelfAdjoint` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L107)). The partial-operator adjoint includes its domain. Essential self-adjointness is the equality of the closure/bidual with the adjoint, while self-adjointness requires the operator itself to equal its adjoint; formal symmetry of the differential expression is weaker.

- **Resolvent set, spectrum, point/continuous/residual spectra**, [DLMF 1.18.Px13.p1](https://dlmf.nist.gov/1.18#Px13.p1):
  `DLMF.AlgebraicAnalytic.shiftedOp` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L112)), `DLMF.AlgebraicAnalytic.opResolventSet` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L116)), `DLMF.AlgebraicAnalytic.opSpectrum` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L123)), `DLMF.AlgebraicAnalytic.opPointSpectrum` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L127)), `DLMF.AlgebraicAnalytic.opContinuousSpectrum` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L132)), `DLMF.AlgebraicAnalytic.opResidualSpectrum` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L139)). The definitions follow injectivity, density of range and a bounded-inverse inequality for z−T. They are actual sets for a supplied partial operator, not automatically a spectral theorem or a globally chosen inverse.

- **Endpoint boundary value and maximal C² operator domain**, [DLMF 1.18.E71](https://dlmf.nist.gov/1.18.E71):
  `DLMF.AlgebraicAnalytic.boundaryValueLeft` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L193)), `DLMF.AlgebraicAnalytic.schrodingerMaxDomainC2` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L199)), `DLMF.AlgebraicAnalytic.wronskianC` ([source](DLMF/AlgebraicAnalytic/Spectral/Basic.lean#L207)). The boundary value is a one-sided limit of αf+βf′. The maximal-domain object records only the C² portion with both f and its differential expression in L²; DLMF’s full distributional maximal domain is broader. A right endpoint analogue is expressed by its corresponding left-limit formula, without another named local boundary-value function.

## Chapter 2 — Asymptotic approximations

Expanded review: all 11 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§2.1–2.11 checked; the matching section is §2.1, including its
five subsections.

### §2.1 Definitions and Elementary Properties

<!-- retained entry 19 -->
- **Asymptotic equivalence**, [2.1.1](https://dlmf.nist.gov/2.1.E1):
  Mathlib `Asymptotics.IsEquivalent` in
  [AsymptoticEquivalent](.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean#L77).
  The normed additive formulation uses a little-o difference; the quotient
  formulation requires the usual eventual nonvanishing interpretation.

<!-- retained entry 20 -->
- **Little-o and big-O**, [2.1.2–3](https://dlmf.nist.gov/2.1.E2):
  Mathlib `Asymptotics.IsLittleO`, `IsBigO` and the explicit-bound `IsBigOWith`
  in [Defs](.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean#L73).
  A within-set limiting filter describes DLMF's approach in `X`; a principal
  filter describes a bound on the whole set. These norm inequalities also cover
  points where the comparison function vanishes.

- **Open and closed sectors for derivative asymptotics**, [DLMF 2.1.ii](https://dlmf.nist.gov/2.1.ii):
  `DLMF.AsymptoticApproximations.rittSector` ([source](DLMF/AsymptoticApproximations/Basics/Basic.lean#L93)), `DLMF.AsymptoticApproximations.rittClosedSector` ([source](DLMF/AsymptoticApproximations/Basics/Basic.lean#L98)) describe the open sector and closed proper subsector used in Ritt’s theorem; they are domain constructions, not additional asymptotic-equivalence predicates.

<!-- retained entry 21 -->
- **Poincaré expansion at infinity**, [2.1.13–15](https://dlmf.nist.gov/2.1.E13):
  `DLMF.AsymptoticApproximations.HasPoincareExpansion` in
  [Basics/Defs](DLMF/AsymptoticApproximations/Basics/Basic.lean#L42), specializing
  `Asymptotics.HasAsymptoticExpansion` to inverse powers and the cobounded
  filter restricted to `X`. A bounded `X` gives a vacuous Lean predicate;
  DLMF assumes an unbounded approach set.

- **Poincaré remainder**, [DLMF 2.1.E13](https://dlmf.nist.gov/2.1.E13):
  `DLMF.AsymptoticApproximations.poincareRemainder` ([source](DLMF/AsymptoticApproximations/Basics/Basic.lean#L89)) is the function after subtracting the first n inverse-power terms. The null expansion of 2.1.17 means that every coefficient is zero; it does not define the represented function uniquely.

<!-- retained entry 22 -->
- **Poincaré expansion at a finite point**, [2.1.16](https://dlmf.nist.gov/2.1.E16):
  `DLMF.AsymptoticApproximations.HasPoincareExpansionAt` in
  [Basics/Defs](DLMF/AsymptoticApproximations/Basics/Basic.lean#L52).
  The related general formal-series construction is
  `Asymptotics.HasAsymptoticPowerSeries` in
  [AsymptoticInversion](DLMFMathlib/Analysis/Asymptotics/AsymptoticInversion.lean#L68).

<!-- retained entry 23 -->
- **Uniform Poincaré expansion**, [2.1.18 and §2.1(iv) prose](https://dlmf.nist.gov/2.1.iv):
  `DLMF.AsymptoticApproximations.HasUniformPoincareExpansion` in
  [Basics/Defs](DLMF/AsymptoticApproximations/Basics/Basic.lean#L59).
  The product filter makes both the bound and the threshold uniform in the
  parameter. There is no separately named finite-point uniform version.

<!-- retained entry 24 -->
- **Asymptotic scale**, [2.1.19](https://dlmf.nist.gov/2.1.E19):
  `Asymptotics.IsAsymptoticScale` in
  [AsymptoticExpansion](DLMFMathlib/Analysis/Asymptotics/AsymptoticExpansion.lean#L55).

<!-- retained entry 25 -->
- **Generalized asymptotic expansion**, [2.1.20–21](https://dlmf.nist.gov/2.1.E20):
  `DLMF.AsymptoticApproximations.HasGeneralizedAsymptoticExpansion` in
  [Basics/Defs](DLMF/AsymptoticApproximations/Basics/Basic.lean#L69).
  Its summands can be functions rather than constant multiples of the scale.
  `Asymptotics.HasAsymptoticExpansion` is the constant-coefficient construction;
  uniform generalized expansions can be expressed by a product filter, but
  have no additional local wrapper.

### §2.2 Transcendental Equations

- **Coefficients for asymptotic reversion**, [DLMF 2.2.E8](https://dlmf.nist.gov/2.2.E8):
  `DLMF.AsymptoticApproximations.lagrangeReversionCoeff` ([source](DLMF/AsymptoticApproximations/Basics/Basic.lean#L78)) constructs F₀=f₀ and the coefficient of x⁻¹ in f(x)ˢ divided by s using a formal power series. The inverse function x(y) is quantified in the reversion theorem; there is no separate canonical inverse chosen from an asymptotic series.

### §2.3 Integrals of a Real Variable

- **Fourier-type and Laplace-type integral families**, [DLMF 2.3.E1](https://dlmf.nist.gov/2.3.E1):
  The integrals I(x)=∫e^{ixt}q(t)dt and ∫e^{−xt}q(t)dt are parameter-dependent instances of interval or half-line integrals. The derivative bounds σₙ in 2.3.3 are suprema in the hypotheses, without a separately named local sequence. The transform objects themselves are catalogued at §1.14.

- **Variation integral**, [DLMF 2.3.E6](https://dlmf.nist.gov/2.3.E6):
  `DLMF.AsymptoticApproximations.variationalOperator` ([source](DLMF/AsymptoticApproximations/Integrals/Basic.lean#L36)) is the oriented interval integral of ‖f′‖; on an increasing interval for a C¹ function it equals total variation. For a reversed interval its sign changes, so it is not the nonnegative variation measure without the appropriate orientation or absolute value.

- **Fractional local expansions and Laplace coefficients**, [DLMF 2.3.E14](https://dlmf.nist.gov/2.3.E14):
  `DLMF.AsymptoticApproximations.cbinom` ([source](DLMF/AsymptoticApproximations/Integrals/Basic.lean#L44)), `DLMF.AsymptoticApproximations.binomSeriesCoeff` ([source](DLMF/AsymptoticApproximations/Integrals/Basic.lean#L48)), `DLMF.AsymptoticApproximations.laplaceCoeff` ([source](DLMF/AsymptoticApproximations/Integrals/Basic.lean#L55)) give the generalized binomial coefficient, the formal coefficient of (P/p₀)^β and the residue-defined bₛ of 2.3.16–18. The latter takes a chosen logarithm L₀ of p₀, preserving the branch required by the complex extension in §2.4. The phase p, amplitude q and their local coefficient sequences remain supplied data.

- **Stationary points and stationary-phase coefficients**, [DLMF 2.3.E19](https://dlmf.nist.gov/2.3.E19):
  A stationary point is a zero of the phase derivative. `DLMF.AsymptoticApproximations.stationaryPhaseP` ([source](DLMF/AsymptoticApproximations/Integrals/Basic.lean#L72)) recursively constructs Pₛ=((1/p′)d/dt)ˢ(q/p′) of 2.3.21. Its divisions are totalized; stationary points are excluded when applying the integration-by-parts formula.

- **Coalescing stationary point and endpoint: Bleistein variables**, [DLMF 2.3.E24](https://dlmf.nist.gov/2.3.E24):
  `DLMF.AsymptoticApproximations.bleisteinA` ([source](DLMF/AsymptoticApproximations/Integrals/Basic.lean#L78)), `DLMF.AsymptoticApproximations.bleisteinB` ([source](DLMF/AsymptoticApproximations/Integrals/Basic.lean#L86)), `DLMF.AsymptoticApproximations.bleisteinW` ([source](DLMF/AsymptoticApproximations/Integrals/Basic.lean#L91)), `DLMF.AsymptoticApproximations.bleisteinF` ([source](DLMF/AsymptoticApproximations/Integrals/Basic.lean#L99)) implement the quadratic normal form parameters a,b, transformed variable w and model integrals Fₛ. The local a has the sign of α, correcting the unsigned square-root shorthand in the printed 2.3.26 so that t=0 maps to w=0 for negative α as required by the prose. The transformed amplitude f(α,w) of 2.3.30 is supplied in the theorem rather than chosen by a global inverse map.

### §2.4 Contour Integrals

- **Bromwich inversion and comparison transforms**, [DLMF 2.4.E2](https://dlmf.nist.gov/2.4.E2):
  `DLMF.AsymptoticApproximations.bromwichPartial` ([source](DLMF/AsymptoticApproximations/Integrals/Basic.lean#L65)) is the truncated vertical-line integral (2πi)⁻¹∫e^{tz}Q(z)dz of 2.4.3. Q and the comparison pair F,f of 2.4.6 are supplied functions with Laplace-transform hypotheses; the finite integral is not itself a selected inverse transform on arbitrary data.

- **Continuous powers along a path and polar asymptotic scale**, [DLMF 2.4.iii](https://dlmf.nist.gov/2.4.iii):
  `DLMF.AsymptoticApproximations.pathPow` ([source](DLMF/AsymptoticApproximations/Integrals/Basic.lean#L104)), `DLMF.AsymptoticApproximations.polarScale` ([source](DLMF/AsymptoticApproximations/Integrals/Basic.lean#L109)) retain a continuous argument along the contour and the independent polar angle of z. They allow more than a principal argument interval and therefore are distinct from silently replacing each power by the principal complex power.

- **Saddles and paths of steepest descent**, [DLMF 2.4.iv](https://dlmf.nist.gov/2.4.iv):
  Saddles are zeros of p′ in the phase e^{−zp}; a steepest-descent contour has constant imaginary part of zp and increasing real part away from the relevant saddle. The local saddle coefficients are the existing logarithm-dependent `DLMF.AsymptoticApproximations.laplaceCoeff` ([source](DLMF/AsymptoticApproximations/Integrals/Basic.lean#L55)). There is no independently selected saddle or contour object for a general phase.

- **Cubic normal form for two coalescing saddles**, [DLMF 2.4.E18](https://dlmf.nist.gov/2.4.E18):
  The Chester–Friedman–Ursell substitution p(α,t)=w³/3+a(α)w²+b(α)w+c(α), its two saddle images and transformed amplitude in 2.4.20 are specified by equations and hypotheses. No general canonical cubic coordinate map or a,b,c construction is selected locally. Airy/Scorer functions used after the further affine change are the Chapter 9 objects, with their existing normalizations.

- **Other coalescing critical configurations**, [DLMF 2.4.vi](https://dlmf.nist.gov/2.4.vi):
  A saddle approaching a pole is modelled by complementary error functions, and a saddle approaching an algebraic endpoint by parabolic cylinder functions. The prose also points to multiple-critical-point canonical integrals in Chapter 36. These are classifications of uniform models, without additional local general-purpose selection predicates.

### §2.5 Mellin Transform Methods

- **Mellin convolution integral**, [DLMF 2.5.E3](https://dlmf.nist.gov/2.5.E3):
  `DLMF.AsymptoticApproximations.mellinConvolutionIntegral` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L165)) implements I(x)=∫₀∞f(t)h(xt)dt, also used at 2.6.54. This is distinct in arguments and measure from the multiplicative Mellin convolution of 1.14.39; its Mellin factorization is a theorem, not a definition by continuation.

- **Bessel-square example and Mellin residue coefficients**, [DLMF 2.5.E8](https://dlmf.nist.gov/2.5.E8):
  `DLMF.AsymptoticApproximations.besselSqMellinKernel` ([source](DLMF/AsymptoticApproximations/Mellin/Basic.lean#L43)), `DLMF.AsymptoticApproximations.besselSqMellinA` ([source](DLMF/AsymptoticApproximations/Mellin/Basic.lean#L49)), `DLMF.AsymptoticApproximations.besselSqMellinB` ([source](DLMF/AsymptoticApproximations/Mellin/Basic.lean#L54)) implement A(z), aₙ=A(n) and bₙ=−A′(n) in 2.5.10–13. The derivative definition continues the coefficient through reciprocal-Gamma zeros, where the displayed digamma product would be 0·∞. The example integral I(x), and cₛ,dₛ of 2.5.16, remain expressions in the corresponding statements; Jν is the existing Bessel construction.

- **Low/high Mellin truncations and continued transforms**, [DLMF 2.5.E21](https://dlmf.nist.gov/2.5.E21):
  `DLMF.AsymptoticApproximations.mellinTruncLow` ([source](DLMF/AsymptoticApproximations/Mellin/Basic.lean#L32)), `DLMF.AsymptoticApproximations.mellinTruncHigh` ([source](DLMF/AsymptoticApproximations/Mellin/Basic.lean#L38)) split f at t=1 (the low definition uses the indicator t≤1; only t>0 enters the Mellin integral). `DLMF.AsymptoticApproximations.IsMellinContinuationOn` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L158)), `DLMF.AsymptoticApproximations.IsMellinContinuation` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L208)) specify supplied holomorphic continuations on their indicated domains. They do not define a new transform by selecting arbitrary values outside a convergence strip. The four convolution pieces Iⱼₖ, their transforms Gⱼₖ and shifted-contour remainders Eⱼₖ in 2.5.30–36 remain finite expressions with the stated domains.

### §2.6 Distributional Methods

- **Stieltjes cube-root example and its missing expansion**, [DLMF 2.6.E1](https://dlmf.nist.gov/2.6.E1):
  `DLMF.AsymptoticApproximations.stieltjesCubeRootExample` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L178)), `DLMF.AsymptoticApproximations.g2b_prod25` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L175)), `DLMF.AsymptoticApproximations.g2b_naiveSum` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L183)), `DLMF.AsymptoticApproximations.g2b_missingSum` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L187)) give the integral S(x), product 2·5···(3s−1) and the fractional-power and integer-power truncated sums of 2.6.6–7. The assigned Gamma-quotient value in 2.6.4 regularizes a divergent integral; it is not an equality with Lean’s totalized Bochner integral outside the ordinary convergence domain.

- **Stieltjes transform and its asymptotic data**, [DLMF 2.6.E8](https://dlmf.nist.gov/2.6.E8):
  `DLMF.AsymptoticApproximations.stieltjesTransform` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L44)), `DLMF.AsymptoticApproximations.IsStieltjesExpansion` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L132)), `DLMF.AsymptoticApproximations.stieltjesRemainder` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L148)) implement the integral transform, the locally integrable asymptotic-data package with 0<α≤1, and fₙ after subtracting n terms. This transform is a separately defined instance of the same integral family already described at §1.14, not an alias to that chapter’s wrapper.

- **Half-line distribution pairing formulas**, [DLMF 2.6.E11](https://dlmf.nist.gov/2.6.E11):
  `DLMF.AsymptoticApproximations.functionPairing` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L57)), `DLMF.AsymptoticApproximations.powPairing` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L63)), `DLMF.AsymptoticApproximations.logPowPairing` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L71)), `DLMF.AsymptoticApproximations.tPowPairing` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L77)) give the integral values assigned to f, t^{−s−α}, t^{−s−1}, and general real powers. These are functions on test functions; their definitions do not assert continuity as Schwartz-space functionals. In particular they are distinct objects from the typed tempered distributions of §1.16, and their defining integrals need convergence hypotheses.

- **Distributional remainder and Mellin moments**, [DLMF 2.6.E15](https://dlmf.nist.gov/2.6.E15):
  `DLMF.AsymptoticApproximations.repeatedTailIntegral` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L92)), `DLMF.AsymptoticApproximations.remainderPairing` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L99)), `DLMF.AsymptoticApproximations.stieltjesDeltaCoeff` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L191)) implement fₙ,ₙ, the associated remainder pairing and cₛ from a supplied Mellin continuation M. Repeated-tail formulas are intended for n≥1; at n=0 the total definition is an integral, not f itself. The Stieltjes delta coefficients are intended at the indices used in 2.6.18.

- **Delta-derivative pairing and logarithmic finite parts**, [DLMF 2.6.E19](https://dlmf.nist.gov/2.6.E19):
  `DLMF.AsymptoticApproximations.diracDerivPairing` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L87)), `DLMF.AsymptoticApproximations.stieltjesLogDeltaCoeff` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L202)), `DLMF.AsymptoticApproximations.stieltjesLogCoeff` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L197)) implement (−1)ˢφ^{(s)}(0), the dₛ coefficients and the punctured-limit finite parts d̃ₛ in 2.6.21 and 2.6.29. The selected `limUnder` value needs an actual limit theorem before it characterizes analytic regularization.

- **Damped Stieltjes test functions and exact remainder**, [DLMF 2.6.E22](https://dlmf.nist.gov/2.6.E22):
  `DLMF.AsymptoticApproximations.stieltjesTestFunction` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L106)), `DLMF.AsymptoticApproximations.stieltjesRemainderTerm` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L153)) give φε(t)=e^{−εt}/(t+z) and Rₙ(z) of 2.6.30. These φε are used only on the positive half-line and are not generally Schwartz functions on the whole real line.

- **Generalized Stieltjes transform and fractional convolution**, [DLMF 2.6.E32](https://dlmf.nist.gov/2.6.E32):
  `DLMF.AsymptoticApproximations.generalizedStieltjesTransform` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L51)), `DLMF.AsymptoticApproximations.riemannLiouvilleIntegral` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L112)), `DLMF.AsymptoticApproximations.halfLineConvolution` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L118)), `DLMF.AsymptoticApproximations.kPlusPairing` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L124)) give the principal-power transform of positive real order ρ, Riemann–Liouville integral of positive real order μ, convolution on [0,x], and pairings for Dⁿf in K⁺. The fractional integral is independent of the complex-order construction in §1.15. K⁺ is represented here by its pairings; no quotient algebra of distributions with its convolution product is constructed.

- **Fractional kernels and remainders**, [DLMF 2.6.E40](https://dlmf.nist.gov/2.6.E40):
  `DLMF.AsymptoticApproximations.IsCompactTest` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L221)), `DLMF.AsymptoticApproximations.g2b_powKernel` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L224)), `DLMF.AsymptoticApproximations.g2b_logKernel` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L227)), `DLMF.AsymptoticApproximations.g2b_repeated` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L232)), `DLMF.AsymptoticApproximations.fractionalRemainder` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L236)), `DLMF.AsymptoticApproximations.g2b_exampleF` ([source](DLMF/AsymptoticApproximations/Distributional/Basic.lean#L243)) record smooth compact tests, power/logarithmic kernels, repeated integrals, the exact finite expression δₙ of 2.6.47 and the example t^{1−α}/(1+t). The kernels use real powers on t>0; their continuations as distributions require the pairing formulas and hypotheses, not the raw function values at t≤0.

- **Mellin regularization and convolution remainders**, [DLMF 2.6.E59](https://dlmf.nist.gov/2.6.E59):
  The formal assignment ∫₀∞t^λdt=0 is part of Mellin regularization, not an ordinary convergent-integral identity. The hₓ and product remainder δₙ of 2.6.60–62 are explicit substitutions/integrals in the convolution statements, without separately selected transform objects.

### §2.7 Differential Equations

- **Second-order equation and singularity classification**, [DLMF 2.7.E1](https://dlmf.nist.gov/2.7.E1):
  `DLMF.AsymptoticApproximations.IsLinearODE2SolOn` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L46)), `DLMF.AsymptoticApproximations.IsLogPlaneSolOn` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L52)) encode the ordinary equation and its lift to z=e^ζ. The prose defines ordinary points by analytic coefficients, regular singular points by removable products (z−z₀)f and (z−z₀)²g, and irregular singular points otherwise. These classes are expressed through analytic hypotheses, rather than separately named local predicates; classification at infinity uses z↦1/z.

- **Indicial equation and Frobenius coefficients**, [DLMF 2.7.E3](https://dlmf.nist.gov/2.7.E3):
  `DLMF.AsymptoticApproximations.indicialPoly` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L60)), `DLMF.AsymptoticApproximations.frobeniusCoeff` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L64)) implement Q(α) and the normalized recurrence a₀=1. Divisions at resonant indices are totalized and are excluded by the nonresonance theorem hypotheses. The logarithmic resonant solution of 2.7.6 is a characterization of supplied solutions, not a second chosen Frobenius-series object.

- **Rank of a meromorphic singularity**, [DLMF 2.7.ii](https://dlmf.nist.gov/2.7.ii):
  `DLMF.AsymptoticApproximations.HasSingularityRank` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L75)) uses the least ℓ≥1 making the two products removable analytic germs, with rank ℓ−1. As written, this predicate can also hold with rank zero at an ordinary point; DLMF’s use of the word singularity additionally assumes the point is singular.

- **Rank-one characteristic data and formal coefficients**, [DLMF 2.7.E7](https://dlmf.nist.gov/2.7.E7):
  `DLMF.AsymptoticApproximations.IsRankOneAtInfinity` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L225)), `DLMF.AsymptoticApproximations.rankOneExponent` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L85)), `DLMF.AsymptoticApproximations.rankOneCoeff` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L91)) encode convergent coefficient expansions at infinity, distinct characteristic roots, exponents μⱼ and normalized formal coefficients. `DLMF.AsymptoticApproximations.rankOneScale` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L220)), `DLMF.AsymptoticApproximations.logSectorFilter` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L215)), `DLMF.AsymptoticApproximations.g2b_logExterior` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L243)) retain the logarithmic plane needed for sectors wider than 2π. Stokes multipliers C₁,C₂ in 2.7.17 are connection constants supplied by existence statements, not independently chosen functions of f,g.

- **Fabry transformation**, [DLMF 2.7.E19](https://dlmf.nist.gov/2.7.E19):
  The exceptional repeated-characteristic-root substitution w=e^{−f₀z/2}W, t=z^{1/2} is expressed directly in the transformation statement; no canonical square-root covering map or selected transformed solution is defined locally.

- **Liouville–Green equation, data and approximants**, [DLMF 2.7.E20](https://dlmf.nist.gov/2.7.E20):
  `DLMF.AsymptoticApproximations.IsLGSolOn` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L256)), `DLMF.AsymptoticApproximations.IsLGData` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L260)), `DLMF.AsymptoticApproximations.lgApproximant` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L252)) specify real solution/data predicates and f^{−1/4}e^{±ξ}, with ξ′=√f. The error-control function F of 2.7.24 is an antiderivative determined up to a constant; its variation is a definite integral in the theorem, not a selected primitive.

- **Recessive, dominant and numerically satisfactory solutions**, [DLMF 2.7.E30](https://dlmf.nist.gov/2.7.E30):
  A recessive/subdominant solution has ratio tending to zero relative to its dominant companion. In a singular neighborhood a numerically satisfactory pair contains a recessive member; on an oscillatory interval the pair has equal asymptotic amplitudes and phase difference π/2. No independent local general predicate selects such pairs; the definitions are descriptive, and decimal examples are excluded: numerical.

### §2.8 Differential Equations with a Parameter

- **Transition and turning points with a large parameter**, [DLMF 2.8.E1](https://dlmf.nist.gov/2.8.E1):
  Transition points are zeros or singularities of f in w″=(u²f+g)w; zeros are turning points. The Liouville change W=ż^{−1/2}w and ψ of 2.8.2–4, and cases ż²f=1,ξ,1/ξ, are expressed by the supplied change of variables and coefficient functions. There is no selected general transition coordinate or ψ construction.

- **Uniform-expansion coefficient families**, [DLMF 2.8.E13](https://dlmf.nist.gov/2.8.E13):
  Case I coefficients Aₛ are given by a derivative/indefinite-integral recurrence with arbitrary integration constants; no canonical A-family is chosen. `DLMF.AsymptoticApproximations.IsAiryCoeffs` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L282)), `DLMF.AsymptoticApproximations.IsBesselCoeffs` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L308)) are structures specifying the Airy and Bessel recurrences of 2.8.17–18 and 2.8.27–31, including derivative witnesses and the separate positive/negative ξ integrals; they are predicates on supplied coefficient families, not functions selecting those families.

- **Airy envelope crossing point and envelopes**, [DLMF 2.8.E19](https://dlmf.nist.gov/2.8.E19):
  `DLMF.AsymptoticApproximations.airyEnvCrit` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L108)), `DLMF.AsymptoticApproximations.envAi` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L114)), `DLMF.AsymptoticApproximations.envBi` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L122)) define the last nonpositive Ai=Bi crossing through a supremum and the piecewise envelopes. The exact crossing condition is mathematical; the printed decimal is excluded: numerical. A supremum definition alone needs its root/existence results before it gives the intended crossing.

- **Bessel envelope crossing point and envelopes**, [DLMF 2.8.E32](https://dlmf.nist.gov/2.8.E32):
  `DLMF.AsymptoticApproximations.besselEnvCrit` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L130)), `DLMF.AsymptoticApproximations.envJ` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L135)), `DLMF.AsymptoticApproximations.envY` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L142)) use an infimum of positive Jν+Yν zeros and the corresponding piecewise real envelopes. The Bessel values are extracted from the complex constructions; the intended nonnegative real order and positive argument are theorem hypotheses.

- **Multiple, fractional and coalescing turning points**, [DLMF 2.8.v](https://dlmf.nist.gov/2.8.v):
  A multiple turning point has an integer multiplicity λ≥2; a fractional one has (z−z₀)^{−λ}f analytic with real λ>−2. The coalescing cases are distinguished by the types of zeros/poles and lead to Bessel, parabolic cylinder or Whittaker models. These general classifications have no additional local selection structures.

### §2.9 Difference Equations

- **Second-order recurrence and its forward difference**, [DLMF 2.9.E1](https://dlmf.nist.gov/2.9.E1):
  `DLMF.AsymptoticApproximations.IsRecurrenceSol` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L202)), `DLMF.AsymptoticApproximations.g2b_fwdDiff` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L188)) specify the three-term recurrence and Δw(n)=w(n+1)−w(n). The equivalent second-order difference equation is a theorem about this predicate.

- **Characteristic exponents and normalized recurrence coefficients**, [DLMF 2.9.E4](https://dlmf.nist.gov/2.9.E4):
  `DLMF.AsymptoticApproximations.differenceExponent` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L151)), `DLMF.AsymptoticApproximations.differenceCoeff` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L157)), `DLMF.AsymptoticApproximations.IsDifferenceCoeffRel` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L175)), `DLMF.AsymptoticApproximations.g2b_invPowScale` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L191)), `DLMF.AsymptoticApproximations.g2b_diffScale` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L194)) give αⱼ, the noncoincident-root recurrence, its implicit relation version and inverse-power scales. In the coincident-root case the division-based coefficient construction is not the intended definition; the relation predicate records the degenerate equations instead.

- **Repeated-root half-power scale and indicial equation**, [DLMF 2.9.E9](https://dlmf.nist.gov/2.9.E9):
  `DLMF.AsymptoticApproximations.g2b_sqrtScale` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L198)) implements ρⁿe^{σκ√n}n^{α−s/2}. The κ,α of 2.9.10 and quadratic indicial roots of 2.9.11 remain supplied expressions/data; no chosen roots or full resonant coefficient family is defined. Recessive/dominant recurrence solutions use the ratio convention of §2.7.

### §2.10 Sums and Sequences

- **Bernoulli periodic kernel and summation remainder**, [DLMF 2.10.i](https://dlmf.nist.gov/2.10.i):
  The periodic Bernoulli function is the existing fractional-part polynomial construction catalogued at §24.2. Euler–Maclaurin and Abel–Plana here are summation identities, not additional function definitions.

- **Logarithmic sum, remainder and Glaisher constant**, [DLMF 2.10.E3](https://dlmf.nist.gov/2.10.E3):
  `DLMF.AsymptoticApproximations.jLogJSum` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L37)), `DLMF.AsymptoticApproximations.jLogJRemainder` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L41)), `DLMF.AsymptoticApproximations.g2b_jLogJTerm` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L116)) give S(n), its convergent tail remainder and expansion terms. The constant C=1/12−ζ′(−1), with e^C called Glaisher’s constant, is the Barnes-family constant recorded at §5.17; it is not newly selected from this asymptotic expansion.

- **Power-sum and harmonic expansion coefficients**, [DLMF 2.10.E7](https://dlmf.nist.gov/2.10.E7):
  `DLMF.AsymptoticApproximations.g2b_powScale` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L120)), `DLMF.AsymptoticApproximations.g2b_powSumCoeff` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L123)), `DLMF.AsymptoticApproximations.g2b_invScale` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L126)), `DLMF.AsymptoticApproximations.g2b_harmonicCoeff` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L129)) give the power scales and exact Bernoulli coefficient sequences. The finite sums use `Finset.sum`; the harmonic number itself is Mathlib’s construction catalogued in Chapter 26.

- **Partial sums and oscillatory power sums**, [DLMF 2.10.E10](https://dlmf.nist.gov/2.10.E10):
  `DLMF.AsymptoticApproximations.partialSumFrom` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L49)), `DLMF.AsymptoticApproximations.oscillatorySum` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L53)) implement Uⱼ=∑₁ʲuᵢ and S(α,β,n)=∑₁^{n−1}e^{ijβ}j^α, including their exact endpoint conventions.

- **Entire ₀F₂ example and contour components**, [DLMF 2.10.E19](https://dlmf.nist.gov/2.10.E19):
  `DLMF.AsymptoticApproximations.hypergeometric0F2OneOne` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L58)), `DLMF.AsymptoticApproximations.g2b_0F2Integrand` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L139)), `DLMF.AsymptoticApproximations.contourIntegralC` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L70)), `DLMF.AsymptoticApproximations.contourIntegralC₁` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L80)), `DLMF.AsymptoticApproximations.contourIntegralC₂` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L86)), `DLMF.AsymptoticApproximations.g2b_semicirclePath` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L62)), `DLMF.AsymptoticApproximations.g2b_segmentPath` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L66)) construct the entire factorial series, its Gamma-integrand and the oriented contour integrals. This is an independent native series representative of the hypergeometric family in Chapter 16; the contour representation is a bridge theorem with convergence hypotheses.

- **Laurent coefficient integral and Darboux comparison**, [DLMF 2.10.E26](https://dlmf.nist.gov/2.10.E26):
  `DLMF.AsymptoticApproximations.laurentCoeff` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L93)), `DLMF.AsymptoticApproximations.legendreComparison` ([source](DLMF/AsymptoticApproximations/Sums/Basic.lean#L99)) construct an annulus-circle Laurent coefficient and the explicit two-branch Legendre comparison function of 2.10.34. The comparison uses factored principal powers to preserve the outward-ray cuts and their values at z=0; its real prefactor is used on 0<α<π. This should not be identified with raw principal powers of e^{±iα}−z on arbitrary α.

### §2.11 Remainder Terms; Stokes Phenomenon

- **Oscillatory rational integral and derivative coefficients**, [DLMF 2.11.E1](https://dlmf.nist.gov/2.11.E1):
  `DLMF.AsymptoticApproximations.cosRationalIntegral` ([source](DLMF/AsymptoticApproximations/Remainders/Basic.lean#L36)), `DLMF.AsymptoticApproximations.cosRationalCoeff` ([source](DLMF/AsymptoticApproximations/Remainders/Basic.lean#L40)) give the exact integral I(m) and qₛ(t) from derivatives of 1/(1+t²). The rounded sample evaluations are excluded: numerical.

- **Terminant and exponential improvement**, [DLMF 2.11.E11](https://dlmf.nist.gov/2.11.E11):
  The scaled generalized exponential integral Fₚ(z)=Γ(p)Eₚ(z)/(2πz^{p−1}) is the terminant used to re-expand a remainder. It is the Chapter 8 terminant normalization, rather than a new canonical sum for a divergent series. Optimum truncation n≈|z|−p+α, exponential improvement and repeated hyperasymptotic re-expansion are asymptotic procedures; no general local data type or automatic truncation selector is defined.

- **Stokes smoothing coefficients and continuous square-root branch**, [DLMF 2.11.E14](https://dlmf.nist.gov/2.11.E14):
  `DLMF.AsymptoticApproximations.stokesA2` ([source](DLMF/AsymptoticApproximations/Remainders/Basic.lean#L55)), `DLMF.AsymptoticApproximations.stokesC` ([source](DLMF/AsymptoticApproximations/Remainders/Basic.lean#L46)), `DLMF.AsymptoticApproximations.stokesH` ([source](DLMF/AsymptoticApproximations/Remainders/Basic.lean#L62)) implement a₂, c(θ) and h₂ₛ from supplied a₂ₛ coefficients. The branch of c is chosen continuously with c(θ)∼π−θ, including c(π)=0, rather than taking the raw principal square root separately at each θ. General a₂ₛ beyond the explicitly constructed a₂ are supplied sequences.

- **Stokes phenomenon, Stokes lines and resurgence**, [DLMF 2.11.iv](https://dlmf.nist.gov/2.11.iv):
  The Stokes phenomenon is the change of elementary asymptotic form of one analytic function between sectors. Stokes lines here are loci of maximum relative dominance, and resurgence means late coefficients reappear through early coefficients of companion expansions. These are descriptive mathematical notions; no general local predicate formalizes them. Repeated re-expansion is called hyperasymptotics in §2.11(v).

- **Whittaker terms and Levin sequence transformation**, [DLMF 2.11.E30](https://dlmf.nist.gov/2.11.E30):
  `DLMF.AsymptoticApproximations.whittakerTerm` ([source](DLMF/AsymptoticApproximations/Remainders/Basic.lean#L70)), `DLMF.AsymptoticApproximations.levinTransform` ([source](DLMF/AsymptoticApproximations/Remainders/Basic.lean#L78)) construct the exact asymptotic term and rational expression dₙ formed from partial sums and forward terms. The latter is recorded as a numerical-method definition; no numerical approximation code is added, and its totalized divisions require nonzero denominator hypotheses for the intended transformation. Euler/Aitken/Wynn transformations are catalogued at §3.9.

## Chapter 3 — Numerical methods

Expanded review: all 12 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§3.1–3.12 checked. No heading contains “Definition” or
“Definitions”. This does not mean the chapter contains no definitions: it
introduces numerical methods under their own headings. Those methods were outside the earlier heading inventory; their mathematical definitions and existing counterparts are considered below, without acquiring numerical code.

### §3.1 Arithmetics and Error Measures

- **Normalized machine numbers, epsilon and range**, [DLMF 3.1.E1](https://dlmf.nist.gov/3.1.E1):
  The sign bit, p-bit significand, exponent interval and zero define the machine-number set ℝfl; εM=2^{1−p}, machine precision 2^{−p}, and Nmin,Nmax specify the normal range. Underflow/overflow refer to leaving that range. Lean’s runtime floating-point types are implementation types, not a verified counterpart to this parameterized mathematical model; no project construction was identified. IEEE format data and decimal precision examples are descriptive only.

- **Chopping and nearest rounding**, [DLMF 3.1.E5](https://dlmf.nist.gov/3.1.E5):
  The adjacent p-bit values x₋,x₊ define chopping/rounding down and symmetric nearest rounding. Tie-breaking is not fixed by this displayed formula. No corresponding parameterized exact rounding map is defined in the project.

- **Interval and exact rational arithmetic**, [DLMF 3.1.E6](https://dlmf.nist.gov/3.1.E6):
  Interval addition, subtraction, multiplication and division are setwise images of the corresponding operation; division excludes intervals containing zero. These are expressible by closed intervals and pointwise set operations in Mathlib, but no numerical interval-arithmetic package is acquired here. Exact rationals use Lean’s `Rat` ([source](.lake/packages/mathlib/Mathlib/Data/Rat/Defs.lean)); the latter is an exact number type, rather than a floating-point approximation.

- **Iterated logarithm and level-index representation**, [DLMF 3.1.E7](https://dlmf.nist.gov/3.1.E7):
  The iterates ln₀x=x, lnℓx=ln(lnℓ₋₁x), and the unique level with lnℓx∈[0,1) define the level-index representation ℓ+a (with a separate sign). No dedicated local level-index representation was identified; a raw iteration of real logarithm needs its admissible-domain hypotheses.

- **Absolute, relative, logarithmic and mollified errors**, [DLMF 3.1.E8](https://dlmf.nist.gov/3.1.E8):
  The exact formulas are |x*−x|, |(x*−x)/x|, |log(x*/x)| and |x*−x|/max(|x|,1). They are expressions using the norm, division, maximum and `Complex.log` ([source](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean#L30)). The relative quantities require the stated nonzero/sign conditions; no separately named project error-measure objects were found.

### §3.2 Linear Algebra

- **Augmented matrix, triangular decomposition and residual**, [DLMF 3.2.E2](https://dlmf.nist.gov/3.2.E2):
  The augmented matrix [A|b], unit-lower triangular L, upper triangular U with A=LU, pivots, elimination multipliers and residual r=b−Ax are matrix constructions or equations. No general selected LU factorization, pivot rule or iterative-refinement sequence is defined locally; the generic matrix objects are catalogued at §1.2.

- **Tridiagonal matrices and elimination recurrences**, [DLMF 3.2.E7](https://dlmf.nist.gov/3.2.E7):
  `DLMF.AlgebraicAnalytic.IsTridiagonal` ([source](DLMF/AlgebraicAnalytic/Algebra/Basic.lean#L71)) is a predicate for a matrix supported on the three central diagonals. The ℓⱼ,dⱼ,yⱼ,xⱼ recurrences of 3.2.10–12 specify the specialized elimination algorithm; no independently named local solver is supplied.

- **Vector and induced matrix norms**, [DLMF 3.2.E13](https://dlmf.nist.gov/3.2.E13):
  The vector p-norm and infinity norm are the standard finite-dimensional ℓp norms. The induced matrix norm is an operator norm after choosing those vector norms; `ContinuousLinearMap.opNorm` ([source](.lake/packages/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean#L170)) supplies the general construction. It should not be confused with the default norm of an unwrapped function-valued matrix, or with the entrywise matrix norm.

- **Linear-system condition number**, [DLMF 3.2.E16](https://dlmf.nist.gov/3.2.E16):
  κ(A)=‖A‖p‖A⁻¹‖p is an exact expression in an induced norm and matrix inverse. No separately named project condition-number function was identified. DLMF assumes A nonsingular; the totalized inverse of a singular matrix is not a conditioning model.

- **Eigenvectors, eigenvalues, characteristic polynomial and nondefectiveness**, [DLMF 3.2.E18](https://dlmf.nist.gov/3.2.E18):
  `Module.End.HasEigenvector` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Eigenspace/Basic.lean#L435)), `Module.End.HasEigenvalue` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Eigenspace/Basic.lean#L443)), `Matrix.charpoly` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean#L140)) are upstream counterparts after passing from a matrix to its linear map. Left eigenvectors use the transpose map, normalized eigenvectors have Euclidean norm one, and multiplicity is root multiplicity of the characteristic polynomial. Nondefective means a full eigenbasis; it is a property, not a selected numerical eigensolver.

- **Eigenvalue condition number**, [DLMF 3.2.E20](https://dlmf.nist.gov/3.2.E20):
  For a simple eigenvalue, κ(λ)=1/|yᵀx| uses normalized left/right eigenvectors with the printed bilinear transpose pairing. No dedicated local condition-number construction was found; for complex data this is not automatically the Hermitian pairing y* x.

- **Lanczos vectors, recurrence coefficients and orthogonality**, [DLMF 3.2.E21](https://dlmf.nist.gov/3.2.E21):
  The recurrences define vⱼ,αⱼ,βⱼ and the symmetric tridiagonal B; S-orthogonality uses vⱼᵀSvₖ=δⱼₖ and the Cholesky factor of S in 3.2.24. No general local Lanczos algorithm or breakdown convention is defined; division by a zero β requires handling outside the displayed nonbreakdown scheme.

### §3.3 Interpolation

- **Lagrange interpolant, basis, nodal polynomial and weights**, [DLMF 3.3.E1](https://dlmf.nist.gov/3.3.E1):
  `Lagrange.interpolate` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Lagrange.lean#L298)), `Lagrange.basis` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Lagrange.lean#L198)), `Lagrange.nodal` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Lagrange.lean#L537)), `Lagrange.nodalWeight` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Lagrange.lean#L632)) give actual upstream polynomial constructions. The divided and barycentric formulas are alternative evaluation identities off the nodes; the polynomial itself is defined at the nodes as well. Distinctness of nodes is essential.

- **Equally spaced interpolation coefficients and error constants**, [DLMF 3.3.E7](https://dlmf.nist.gov/3.3.E7):
  The integer endpoints n₀,n₁, parity σ, coefficients Aₖⁿ(t) and maxima cₙ of 3.3.8–12 are exact specializations of Lagrange interpolation. No separate local A/c family is defined. The two- through eight-point formulas specialize these objects; decimal error constants are excluded: numerical.

- **Divided differences and confluent values**, [DLMF 3.3.E34](https://dlmf.nist.gov/3.3.E34):
  The recursive divided differences and their sum of inverse nodal products define [z₀,…,zₙ]f. Newton interpolation uses the same interpolant, and repeated nodes have derivative/factorial limits under regularity hypotheses. The Lagrange construction is upstream, but no independently named general divided-difference/confluent-family construction was identified locally. Mathlib `dslope` ([source](.lake/packages/mathlib/Mathlib/Analysis/Calculus/DSlope.lean)) provides the two-node divided difference with derivative on the diagonal; it does not construct arbitrary-order confluent differences.

- **Inverse interpolation**, [DLMF 3.3.E39](https://dlmf.nist.gov/3.3.E39):
  Interchanging nodes and function values defines the inverse interpolating polynomial, using the same `Lagrange.interpolate` ([source](.lake/packages/mathlib/Mathlib/LinearAlgebra/Lagrange.lean#L298)) on the exchanged data when its nodes are distinct. It is not a global functional inverse of f; the Airy decimal example is excluded: numerical.

- **Cardinal interpolation and Sinc kernel**, [DLMF 3.3.E43](https://dlmf.nist.gov/3.3.E43):
  C(f,h)(x)=∑ₖ∈ℤf(kh)S(k,h)(x), with S=sin(π(x−kh)/h)/(π(x−kh)/h), is the cardinal series. `Real.sinc` ([source](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Sinc.lean#L40)) supplies the removable value one at zero, so S=Real.sinc(π(x−kh)/h) for h≠0. No general named cardinal-series object was found; convergence is a separate requirement.

### §3.4 Differentiation

- **Differentiated Lagrange weights and finite-difference stencils**, [DLMF 3.4.E2](https://dlmf.nist.gov/3.4.E2):
  Bₖⁿ=(Aₖⁿ)′ gives the differentiated interpolation weights, with explicit two- through eight-point specializations. The grid notation uₜ,ₛ=u(x₀+th,y₀+sh) in §3.4(iii) and the first/second/fourth derivative stencils are finite formulas, without selected local numerical differentiation routines.

- **Laplacian and biharmonic operator**, [DLMF 3.4.E27](https://dlmf.nist.gov/3.4.E27):
  ∇²u=uₓₓ+uᵧᵧ and ∇⁴u=uₓₓₓₓ+2uₓₓᵧᵧ+uᵧᵧᵧᵧ repeat the differential operators catalogued at §1.5. The displayed lattice combinations define approximation stencils, not alternative exact differential operators.

### §3.5 Quadrature

- **Trapezoidal, Simpson and Romberg constructions**, [DLMF 3.5.E1](https://dlmf.nist.gov/3.5.E1):
  The weighted endpoint sums in 3.5.1–2 and 3.5.6–7 define elementary/composite trapezoidal and Simpson rules; Gₖ(h) in 3.5.10–12 recursively defines Romberg extrapolation. Mathlib `trapezoidal_integral` and `trapezoidal_error` ([source](.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/TrapezoidalRule.lean#L40)) construct the composite rule and its signed difference from the integral, with N trapezoids and N+1 evaluations (N>0 intended). N=1 gives the elementary rule. No dedicated local Simpson/Romberg algorithm is defined. Exact error formulas and convergence conditions remain mathematical statements; no decimal computation is acquired.

- **Interpolatory, open and closed quadrature rules**, [DLMF 3.5.E15](https://dlmf.nist.gov/3.5.E15):
  An interpolatory rule integrates all polynomials of degree≤n−1 exactly; closed rules include both endpoints, open rules have all nodes inside. Newton–Cotes, midpoint and Fejér rules are the indicated node choices. Clenshaw–Curtis nodes cos(kπ/n), endpoint factors gₖ, parity factors bⱼ and weights in 3.5.16–17 define a particular closed rule. No independently named local family was found.

- **Gaussian nodes, Christoffel numbers and error constant**, [DLMF 3.5.E18](https://dlmf.nist.gov/3.5.E18):
  For monic orthogonal pₙ, nodes are its roots, Christoffel weights are the integrals of its nodal basis, and γₙ=∫pₙ²w. The Legendre, four Chebyshev, Jacobi, Laguerre, Hermite and logarithmic-weight rules of 3.5.21–29 specialize interval and weight; no general local rule object selects these nodes/weights. The underlying exact orthogonal polynomials exist as catalogued in Chapter 18; the decimal node tables are excluded: numerical.

- **Monic/orthonormal recurrences and Jacobi matrix**, [DLMF 3.5.E30](https://dlmf.nist.gov/3.5.E30):
  The qₙ=pₙ/√hₙ normalization, symmetric Jacobi matrix Jₙ, eigenvector weights β₀vₖ,₁² and recurrence coefficients αₙ,βₙ (3.5.33_1–3 and Table 3.5.17_5) describe exact Gaussian data. These are expressions in the existing orthogonal-polynomial families, not independently selected numerical eigensystems. Laguerre’s chosen qₙ includes the sign (−1)ⁿ in the positive-off-diagonal convention.

- **Oscillatory, complex Gaussian and contour quadrature**, [DLMF 3.5.E34](https://dlmf.nist.gov/3.5.E34):
  Filon’s rule applies to sine/cosine-weighted integrals; Longman’s method splits alternating subintegrals. The Bromwich functional I(f) in 3.5.35 and reciprocal-variable orthogonal polynomials of 3.5.37 define complex Gaussian data related to Bessel polynomials. No new local numerical method object is defined. Laplace, Hilbert and erfc contour integrals in the examples are representations of the existing functions/transforms, with their stated branches and principal-value conventions.

- **Cubature on a disk or square and Monte Carlo sampling**, [DLMF 3.5.E47](https://dlmf.nist.gov/3.5.E47):
  Normalized area integrals define the target functionals; Table 3.5.21 supplies exact symmetric nodes and weights for finite cubature rules. Standard Monte Carlo means uniform sampling from the integration region; importance sampling changes the distribution toward large contributions. No cubature/sampling code or numerical tables are acquired.

### §3.6 Linear Difference Equations

- **Linear difference equations and minimal solutions**, [DLMF 3.6.E1](https://dlmf.nist.gov/3.6.E1):
  The forward difference Δwₙ=wₙ₊₁−wₙ and its iterate express the homogeneous/inhomogeneous equation. The root-shifted homogeneous recurrence counterpart is `DLMF.AsymptoticApproximations.IsRecurrenceSol` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L202)), `DLMF.AsymptoticApproximations.g2b_fwdDiff` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L188)). A minimal/recessive/distinguished solution has ratio tending to zero against an independent dominant solution and is normalized only up to a constant.

- **Miller and Olver sequences**, [DLMF 3.6.iii](https://dlmf.nist.gov/3.6.iii):
  Miller’s method starts a trial backward recurrence and applies a normalizing factor Λ determined by a value or linear sum. Olver’s pₙ,eₙ and finite-system wₙ⁽ᴺ⁾ are defined by 3.6.7–10 with the prescribed initial/boundary data and stopping test. No general local algorithm selects them; first- and higher-order equations in 3.6.17–18 are corresponding recurrence forms. Special-function examples use the existing Bessel and Weber functions.

### §3.7 Ordinary Differential Equations

- **Inhomogeneous ODE and derivative-transfer coefficients**, [DLMF 3.7.E1](https://dlmf.nist.gov/3.7.E1):
  The equation w″+fw′+gw=h, derivative coefficients fₛ,gₛ,hₛ of 3.7.2–4, Taylor transfer matrix A(τ,z), vector b(τ,z) and band system Aₚ of 3.7.6–12 are mathematically defined by the displayed recurrences and series. No general named local derivative-transfer algorithm is supplied; general ODE solution predicates are catalogued in Chapters 1–2.

- **Sturm–Liouville eigenvalue problem**, [DLMF 3.7.E15](https://dlmf.nist.gov/3.7.E15):
  Nontrivial solutions of w″+(λ−q)w=0 with vanishing endpoint limits define eigenvalues λₖ and eigenfunctions wₖ in this Dirichlet setting. The generic endpoint/eigenvalue predicates of §1.13 and Chapter 28–30 specializations are counterparts; no independent general function selecting this numerical spectral sequence is defined in Chapter 3.

- **Fourth-order Runge–Kutta stages**, [DLMF 3.7.E18](https://dlmf.nist.gov/3.7.E18):
  The k₁,…,k₄ stage formulas in 3.7.19 and 3.7.21 define the first- and second-order fourth-order schemes. No corresponding numerical integrator is introduced locally; the O(h⁵) remainder is an error assertion under smoothness assumptions.

### §3.8 Nonlinear Equations

- **Simple/multiple zeros, fixed points and convergence order**, [DLMF 3.8.E1](https://dlmf.nist.gov/3.8.E1):
  Zeros and their analytic multiplicity repeat §1.10; `Function.IsFixedPt` ([source](.lake/packages/mathlib/Mathlib/Logic/Function/Defs.lean#L214)) is the exact fixed-point predicate. Convergence order p is defined by the eventual error inequality with p the largest allowed exponent; local convergence quantifies a neighborhood of admissible initial points. These convergence-order/local-basin notions have no dedicated general local wrapper.

- **Newton, bisection, secant and Steffensen maps**, [DLMF 3.8.E4](https://dlmf.nist.gov/3.8.E4):
  `Polynomial.newtonMap` ([source](.lake/packages/mathlib/Mathlib/Dynamics/Newton.lean#L44)) is an actual upstream Newton map for polynomials; it uses inverse-of-unit totalization and fixes points where the derivative is not a unit. DLMF’s general differentiable Newton map, modified multiple-root map, bisection, regula falsi/secant and Steffensen iteration of 3.8.6–7 remain formulas without additional local selected algorithms.

- **Bairstow quadratic-factor iteration and Halley map**, [DLMF 3.8.E10](https://dlmf.nist.gov/3.8.E10):
  The qⱼ,rⱼ recurrences and Δs,Δt,ℓ of 3.8.10–11 define Bairstow’s quadratic-factor update. Halley’s rational derivative update is 3.8.12. No named local algorithms were found. Polynomial deflation is division by the located factor; Wilkinson’s ∏ⱼ₌₁²⁰(x−j) is an explicit example, not a separately named local polynomial.

- **Iteration basins and Julia boundary**, [DLMF 3.8.viii](https://dlmf.nist.gov/3.8.viii):
  The text describes the boundaries separating basins of convergence of the fixed-point iteration, calling the resulting dynamical boundary a Julia set and describing self-similarity. No local complex-dynamical construction was identified. This descriptive passage is not being promoted to a blanket theorem that every analytic function has a self-similar boundary.

### §3.9 Acceleration of Convergence

- **Limit-preserving and accelerating transformations**, [DLMF 3.9.E1](https://dlmf.nist.gov/3.9.E1):
  A transformation preserves a sequence limit σ if its output has the same limit, and accelerates if (tₙ−σ)/(sₙ−σ)→0. These are expressible using `Filter.Tendsto` and asymptotic equivalence/little-o; no general sequence-transform structure is defined locally.

- **Euler transformation and iterated forward differences**, [DLMF 3.9.E3](https://dlmf.nist.gov/3.9.E3):
  Δᵏa₀ is the recursively iterated forward difference, also an alternating binomial sum; Euler’s transformed series weights it by (−1)ᵏ2^{−k−1}. `DLMF.AsymptoticApproximations.g2b_fwdDiff` ([source](DLMF/AsymptoticApproximations/ODE/Basic.lean#L188)) supplies one forward difference. Mathlib `fwdDiff` ([source](.lake/packages/mathlib/Mathlib/Algebra/Group/ForwardDiff.lean#L40)) defines the general increment operator; its iterates give Δᵏ. TauCeti `TauCeti.fwdDiffList` ([source](.lake/packages/TauCeti/TauCeti/Analysis/CompletelyMonotone/FiniteDifference/Basic.lean#L87)) also allows distinct increments. No separate general Euler series-transformation object was found.

- **Aitken, Shanks and Wynn transformations**, [DLMF 3.9.E7](https://dlmf.nist.gov/3.9.E7):
  Aitken’s rational Δ² update, Hankel determinants Hₘ(uₙ), Shanks ratios and Wynn’s ε-table recurrence are the exact constructions of 3.9.7–11. No dedicated local general constructions were identified. Their denominator/nonvanishing conditions matter; an arbitrary totalized quotient is not a guarantee of limit preservation.

- **Levin/Weniger weights and logarithmic convergence**, [DLMF 3.9.E13](https://dlmf.nist.gov/3.9.E13):
  The general two-index Levin transform and power weights cⱼ,ₖ,ₙ are defined by 3.9.13–14; Weniger’s variants use rising-factorial weights in 3.9.16–17. `DLMF.AsymptoticApproximations.levinTransform` ([source](DLMF/AsymptoticApproximations/Remainders/Basic.lean#L78)) is the n=0 one-index variant from 2.11.32, with the common weight factor cancelled, not an implementation of every variant. Logarithmic convergence means the successive error ratio tends to one.

### §3.10 Continued Fractions

- **Convergents and conversion of a series**, [DLMF 3.10.E1](https://dlmf.nist.gov/3.10.E1):
  The generalized continued fraction, numerator/denominator recurrences and convergents are the Chapter 1.12 objects. The explicit bₙ,aₙ derived from nonzero uₙ in 3.10.5 define one series-to-fraction conversion; no separate local conversion algorithm is selected.

- **Stieltjes/Jacobi fractions and formal correspondence**, [DLMF 3.10.E6](https://dlmf.nist.gov/3.10.E6):
  An S-fraction has numerator −aₙz at each unit denominator; a J-fraction has linear denominator 1−αₙz and quadratic numerator −βₙz². Correspondence/association requires agreement through z^{n−1}/z^{2n−1} for successive convergents. These are special forms of the existing generalized fraction; no separate general local S/J-fraction class or formal-correspondence predicate was identified.

- **Quotient-difference, backward, series and Steed recurrences**, [DLMF 3.10.E8](https://dlmf.nist.gov/3.10.E8):
  The q/e rhombus scheme of 3.10.8–10, backward denominators uₖ, forward-series tₖ/ρₖ and Steed Dₙ/∇Cₙ of 3.10.12–17 define exact algorithmic sequences. No general local numerical algorithms are added. Continued-fraction specializations already constructed for the individual functions retain their own convergence and exceptional-denominator conditions.

### §3.11 Approximation Techniques

- **Minimax polynomial and equioscillation data**, [DLMF 3.11.i](https://dlmf.nist.gov/3.11.i):
  The minimax polynomial minimizes the uniform norm of f−p among degree≤n polynomials. The extrema xⱼ, signed errors mⱼ and coefficient corrections δaₖ define an exchange step. No local general minimax selector or Remez polynomial iteration is supplied; these are approximation notions recorded descriptively.

- **Chebyshev coefficients, rescaling and Clenshaw recurrence**, [DLMF 3.11.E6](https://dlmf.nist.gov/3.11.E6):
  `Polynomial.Chebyshev.T` ([source](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Chebyshev.lean#L67)) constructs the exact polynomial family. The coefficients cₙ=(2/π)∫₀πf(cosθ)cos(nθ)dθ, half-weighted c₀ series, interval rescaling and Clenshaw uₖ recurrence of 3.11.10–15 are additional mathematical constructions without separate local generic wrappers. Fourier coefficient machinery gives the corresponding integral after normalization; convergence is a theorem.

- **Weighted minimax rational approximation**, [DLMF 3.11.E16](https://dlmf.nist.gov/3.11.E16):
  Rₖ,ℓ is a quotient of bounded-degree polynomials minimizing |(R−f)/w| on the interval; mⱼ and the equioscillation points specify the exchange data. No selected generic local best-rational-approximation object or Remez second algorithm was identified. Rounded fitted coefficients are excluded: numerical.

- **Padé approximant, table and cross rule**, [DLMF 3.11.E21](https://dlmf.nist.gov/3.11.E21):
  A Padé approximant satisfies N−fD=O(z^{p+q+1}) with numerator/denominator degrees bounded by p,q. The array indexed by these degrees is the Padé table, and Wynn’s five-point reciprocal relation computes its entries where defined. No generic local Padé construction was identified; individual special-function continued-fraction convergents may be linked by theorems without defining the general Padé object.

- **Discrete weighted least squares and normal-equation moments**, [DLMF 3.11.E27](https://dlmf.nist.gov/3.11.E27):
  The polynomial or basis combination minimizes a finite sum of squared residuals; Xₖ,Fₖ and Xₖℓ,Fₖ in 3.11.30–35 are weighted moments and Gram-matrix entries. These are finite sums/inner products, without a selected general local fitting algorithm. Gram–Schmidt provides generic orthogonalization, with rank assumptions for uniqueness.

- **Discrete Fourier pair and Fourier matrix**, [DLMF 3.11.E39](https://dlmf.nist.gov/3.11.E39):
  Mathlib `ZMod.dft` ([source](.lake/packages/mathlib/Mathlib/Analysis/Fourier/ZMod.lean#L87)) is the exact finite transform with negative exponential and counting-measure normalization. DLMF’s aₖ is (1/n) times that transform of f; the inverse uses the positive exponential. The Fourier matrix uses ωₙ=e^{2πi/n}; FFT is a factorization/evaluation method for this same transform, not a different mathematical transform.

- **Splines and cubic Bézier curves**, [DLMF 3.11.vi](https://dlmf.nist.gov/3.11.vi):
  A spline is a piecewise polynomial determined by node and smoothness/interpolation conditions. Cubic Bézier coordinates use four points, two endpoints and two controls, with the stated endpoint tangent directions. No dedicated local spline/Bézier construction was found; polynomial functions and piecewise gluing alone do not supply a chosen interpolating spline.

### §3.12 Mathematical Constants

- **Analytic constants π, e and Euler’s γ**, [DLMF 3.12.E2](https://dlmf.nist.gov/3.12.E2):
  `Real.pi` ([source](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean#L128)), `Real.exp` ([source](.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean#L81)), `Real.eulerMascheroniConstant` ([source](.lake/packages/mathlib/Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean#L130)) are the existing exact upstream constructions, with e=exp(1). The arctangent integral in 3.12.2 is an equivalent characterization of π, not a new independently named integral definition. Decimal listings and high-precision databases are excluded: numerical.

## Chapter 4 — Elementary functions

Expanded review: all 48 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§4.1–4.48 checked; matching headings are §4.2, §4.14,
§4.23(i), §4.28, and §4.37(i).

### §4.2 Definitions

<!-- retained entry 26 -->
- **General logarithm, principal logarithm, and the two banks of the closed
  principal cut**, [4.2.1–7](https://dlmf.nist.gov/4.2.i):
  `DLMF.Elementary.generalLogValues`, `logSheet`, `closedLogValues`, and
  `logBranchCut` in [LogExpBasic](DLMF/Elementary/LogExpBasic.lean#L56);
  Mathlib `Complex.log` and `Real.log` are the single-valued complex and real
  functions, defined in
  [Complex/Log](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean#L30)
  and [Log/Basic](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean).
  `Complex.log` selects the upper bank of the negative axis;
  `closedLogValues` retains both values. No separate arbitrary-path integral
  logarithm is defined.

<!-- retained entry 27 -->
- **Logarithm to base a**, [4.2.8](https://dlmf.nist.gov/4.2.E8):
  `DLMF.Elementary.complexLogb` in
  [LogExpBasic](DLMF/Elementary/LogExpBasic.lean#L321), and Mathlib `Real.logb`
  in [Log/Base](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Base.lean#L44).
  The complex definition divides principal logarithms and inherits their cuts.

<!-- retained entry 28 -->
- **Natural base e and exponential**, [4.2.12–13](https://dlmf.nist.gov/4.2.E12),
  [4.2.19](https://dlmf.nist.gov/4.2.E19): Mathlib `Real.exp 1`, `Real.exp`,
  `Complex.exp` in
  [Complex/Exponential](.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean#L63),
  and the general Banach-algebra `NormedSpace.exp` in
  [Normed/Algebra/Exponential](.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/Exponential.lean).
  The decimal values in 4.2.11, 4.2.17 and 4.2.18 are numerical, not additional
  definition objects in this inventory.

<!-- retained entry 29 -->
- **General and principal powers**, [4.2.26–28](https://dlmf.nist.gov/4.2.E26):
  `DLMF.Elementary.generalPowerValues` and `closedPowerValues` in
  [LogExpBasic](DLMF/Elementary/LogExpBasic.lean#L364);
  Mathlib `Complex.cpow` selects the principal logarithm, `Real.rpow` treats
  real powers, and ordinary natural/integer powers cover the single-valued
  cases. The definitions are in
  [Pow/Complex](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean)
  and [Pow/Real](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean).
  `Complex.sqrt` in [RCLike/Sqrt](.lake/packages/mathlib/Mathlib/Analysis/RCLike/Sqrt.lean#L26)
  is the principal square root mentioned in 4.2.37.
  The set-valued local constructions preserve DLMF's two-bank convention.

### §4.9 Continued Fractions

- **Exponential-polynomial continued-fraction auxiliary**, [DLMF 4.9.E5](https://dlmf.nist.gov/4.9.E5):
  eₙ(z)=Σ_{k=0}ⁿzᵏ/k! is `DLMF.Elementary.expPartialSum` ([source](DLMF/Elementary/LogExpIntegrals.lean#L70)). A second actual exponential partial-sum construction appears in Chapter 8; the separate Chapter 8 construction is catalogued at its source position.

  [DLMF 4.9.E5](https://dlmf.nist.gov/4.9.E5):
  The exponential polynomial of degree n.
  `DLMF.Elementary.expPartialSum` ([definition](DLMF/Elementary/LogExpIntegrals.lean#L70)).

### §4.12 Generalized Logarithms and Exponentials

- **Generalized exponential/logarithm and chosen iteration count**, [DLMF 4.12](https://dlmf.nist.gov/4.12):
  `DLMF.Elementary.IsGeneralizedExpLog` packages the inverse relation, normalization, recurrence and monotonicity. The specific piecewise choice linear on [0,1], with iterated exp/log outside, is `DLMF.Elementary.generalizedExp`, `DLMF.Elementary.generalizedLog`, with `DLMF.Elementary.logIterationCount` ([source](DLMF/Elementary/Generalized.lean#L48)). DLMF does not claim uniqueness among all generalized exp/log pairs. These exact objects are mathematical definitions even though generalized arithmetic is one motivation.

### §4.13 Lambert W -Function

- **Lambert branch, Wright omega, tree function and coefficient families**, [DLMF 4.13](https://dlmf.nist.gov/4.13):
  The actual branch-family auxiliaries include `DLMF.Elementary.lambertWLower`, `DLMF.Elementary.wrightOmega`, `DLMF.Elementary.treeT`, `DLMF.Elementary.lambertXi`, `DLMF.Elementary.lambertDerivPolynomial`, `DLMF.Elementary.lambertC`, `DLMF.Elementary.lambertD`, `DLMF.Elementary.lambertWOver`, and `DLMF.Elementary.lambertAsymptoticTerm` ([source](DLMF/Elementary/LambertW/BranchesAndCalculus.lean#L396)). They cover the lower-bank continuation, Wright ω, principal tree T, logarithmic branch variable ξₖ, derivative polynomials, both branch-point coefficient recurrences, the removable W₀(z)/z value, and large-argument series terms. The general branch existence specification remains admitted; a selected value is not by itself a proved inverse/analytic branch.

  [DLMF 4.13.E4_2](https://dlmf.nist.gov/4.13.E4_2):
  Derivative polynomials, given by their full recurrence (4.13.4_2).
  `DLMF.Elementary.lambertDerivPolynomial` ([definition](DLMF/Elementary/LambertW/BranchesAndCalculus.lean#L415)).

<!-- retained entry 30 -->
- **Lambert integer branches Wₖ and upper/lower cut values**,
  [4.13.1 and branch prose](https://dlmf.nist.gov/4.13.E1):
  `DLMF.Elementary.lambertW`, `lambertWLower`, with
  `LambertBranchFamily` and `lambertPrincipalDomain`, in
  [BranchesAndCalculus](DLMF/Elementary/LambertW/BranchesAndCalculus.lean#L392).
  The family is selected using `exists_lambertBranchFamily` in
  [BranchesAndCalculus](DLMF/Elementary/LambertW/BranchesAndCalculus.lean#L342),
  which remains admitted. The structure specifies analytic domains,
  basepoint normalization and upper-side boundary values; `lambertWLower`
  applies conjugation and k→−k. Nonprincipal values at zero are totalized.

<!-- retained entry 31 -->
- **Wright omega and tree T**,
  [4.13.1_2–1_3](https://dlmf.nist.gov/4.13.E1_2):
  `DLMF.Elementary.wrightOmega`, `treeT` in
  [BranchesAndCalculus](DLMF/Elementary/LambertW/BranchesAndCalculus.lean#L399).
  Omega selects the integer unwinding branch using the imaginary part of z;
  T is −W₀(−z). Both inherit the admitted branch-family construction.

### §4.14 Definitions and Periodicity

<!-- retained entry 32 -->
- **Sine and cosine**, [4.14.1–2](https://dlmf.nist.gov/4.14.E1): Mathlib
  `Complex.sin`, `Complex.cos`, `Real.sin`, and `Real.cos` in
  [Complex/Trigonometric](.lake/packages/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean#L29).

<!-- retained entry 33 -->
- **Tangent, cosecant, secant and cotangent**, [4.14.4–7](https://dlmf.nist.gov/4.14.E4):
  Mathlib `Complex.tan`, `Complex.cot`, `Real.tan`, `Real.cot`, and
  `DLMF.Elementary.csc`, `sec` in
  [DirectIdentities](DLMF/Elementary/Trigonometric/DirectIdentities.lean#L86).
  The real cosecant/secant are expressible as inverse sine/cosine; there is no
  additional local real wrapper. Quotients have totalized values at poles.

### §4.20 Derivatives and Differential Equations

- **Linear oscillator equation, with a nonzero complex frequency**, [DLMF 4.20.E9](https://dlmf.nist.gov/4.20.E9):
  The linear oscillator equation, with a nonzero complex frequency.
  `DLMF.Elementary.IsTrigLinearSolution` ([definition](DLMF/Elementary/Trigonometric/DirectIdentities.lean#L693)).

- **Trigonometric energy equation**, [DLMF 4.20.E10](https://dlmf.nist.gov/4.20.E10):
  The trigonometric energy equation.
  `DLMF.Elementary.IsTrigEnergySolution` ([definition](DLMF/Elementary/Trigonometric/DirectIdentities.lean#L698)).

- **Trigonometric Riccati equation, considered away from poles of solutions**, [DLMF 4.20.E11](https://dlmf.nist.gov/4.20.E11):
  The trigonometric Riccati equation, considered away from poles of solutions.
  `DLMF.Elementary.IsTrigRiccatiSolution` ([definition](DLMF/Elementary/Trigonometric/DirectIdentities.lean#L703)).

### §4.23 Inverse Trigonometric Functions

<!-- retained entry 34 -->
- **General arcsine, arccosine, arctangent, arccosecant, arcsecant and
  arccotangent**, [4.23.1–6](https://dlmf.nist.gov/4.23.i):
  `DLMF.Elementary.arcsinGeneral`, `arccosGeneral`, `arctanGeneral`,
  `arccscGeneral`, `arcsecGeneral`, and `arccotGeneral` in
  [InverseBranches](DLMF/Elementary/Trigonometric/InverseBranches.lean#L65).
  These are inverse-relation sets, not path-dependent integral objects.
  Their principal counterparts are `arcsinPrincipal`, `arccosPrincipal`,
  `arccscPrincipal`, `arcsecPrincipal`, `arccotPrincipal`, and Mathlib
  `Complex.arctan` in
  [Complex/Arctan](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Arctan.lean#L30);
  Mathlib also supplies `Real.arcsin`, `Real.arccos`,
  `Real.arctan` in
  [Trigonometric/Inverse](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Inverse.lean)
  and [Arctan](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Arctan.lean).
  Explicit cut-bank functions `arcsinRightBank`,
  `arcsinLeftBank`, and `arctanCutBank` retain boundary choices.

- **Inverse-trigonometric distance variables and Gudermannian pair**, [DLMF 4.23.E37](https://dlmf.nist.gov/4.23.E37):
  α,β in the real/imaginary part formulas are `DLMF.Elementary.inverseTrigAlpha`, `DLMF.Elementary.inverseTrigBeta` ([source](DLMF/Elementary/Trigonometric/InverseIdentities.lean#L84)); the Gudermannian and its inverse are `DLMF.Elementary.gudermannian`, `DLMF.Elementary.inverseGudermannian` ([source](DLMF/Elementary/Trigonometric/InverseIdentities.lean#L341)). The integral and elementary expressions are representation bridges, with the inverse defined on its open interval. The explicit bank functions for arcsin/arctan belong with their defining cut values; an ordinary single-valued principal function chooses one bank on the cut.

  [DLMF 4.23.E37](https://dlmf.nist.gov/4.23.E37):
  The half-sum of distances to the inverse sine branch points.
  `DLMF.Elementary.inverseTrigAlpha` ([definition](DLMF/Elementary/Trigonometric/InverseIdentities.lean#L84)).

  [DLMF 4.23.E38](https://dlmf.nist.gov/4.23.E38):
  The half-difference of distances to the inverse sine branch points.
  `DLMF.Elementary.inverseTrigBeta` ([definition](DLMF/Elementary/Trigonometric/InverseIdentities.lean#L88)).

  [DLMF 4.23.E39](https://dlmf.nist.gov/4.23.E39):
  The Gudermannian, real and odd on the full real line.
  `DLMF.Elementary.gudermannian` ([definition](DLMF/Elementary/Trigonometric/InverseIdentities.lean#L341)).

  [DLMF 4.23.E41](https://dlmf.nist.gov/4.23.E41):
  The inverse Gudermannian on the open strip (-pi/2,pi/2).
  `DLMF.Elementary.inverseGudermannian` ([definition](DLMF/Elementary/Trigonometric/InverseIdentities.lean#L345)).

### §4.28 Definitions and Periodicity

<!-- retained entry 35 -->
- **Hyperbolic sine, cosine and tangent**, [4.28.1–4](https://dlmf.nist.gov/4.28.E1):
  Mathlib `Complex.sinh`, `Complex.cosh`, `Complex.tanh`, `Real.sinh`,
  `Real.cosh`, `Real.tanh` in
  [Complex/Trigonometric](.lake/packages/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean#L49).

<!-- retained entry 36 -->
- **Hyperbolic cosecant, secant and cotangent**, [4.28.5–7](https://dlmf.nist.gov/4.28.E5):
  `DLMF.Elementary.csch`, `sech`, and `coth` in
  [IdentitiesAndSeries](DLMF/Elementary/Hyperbolic/IdentitiesAndSeries.lean#L35).
  Real restrictions are expressions through these quotients, without separate
  local real definitions.

### §4.37 Inverse Hyperbolic Functions

<!-- retained entry 37 -->
- **General inverse sinh, cosh, tanh, csch, sech and coth**, [4.37.1–6](https://dlmf.nist.gov/4.37.i):
  `DLMF.Elementary.arcsinhValues`, `arccoshValues`, `arctanhValues`,
  `arccschValues`, `arcsechValues`, and `arccothValues` in
  [IdentitiesAndSeries](DLMF/Elementary/Hyperbolic/IdentitiesAndSeries.lean#L72).
  Principal logarithmic formulas are separately defined there as `arcsinh`,
  `arccosh`, `arctanh`, `arccsch`, `arcsech`, `arccoth`.
  Mathlib `Real.arsinh` in
  [Arsinh](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Arsinh.lean#L54)
  is an independent real construction. The local complex
  objects select branches; their value sets encode the full inverse relations.

### §4.42 Solution of Triangles

- **Triangle semiperimeter and cubic auxiliary parameters**, [DLMF 4.42.E7](https://dlmf.nist.gov/4.42.E7):
  The triangle semiperimeter is s=(a+b+c)/2, an expression rather than a dedicated local function. §4.43 likewise introduces the stated p,q-dependent cubic scales before giving trigonometric/hyperbolic root formulas; no separate local choice of cubic-root enumeration was found in the elementary modules. Einstein/Planck functions are only mentioned by reference in §4.44, without their formulas or new local constructions.

### §4.45 Methods of Computation

- **Exact argument-reduction constructions**, [DLMF 4.45](https://dlmf.nist.gov/4.45):
  `DLMF.Elementary.logReductionArgument`, `DLMF.Elementary.expReductionIndex`, `DLMF.Elementary.expReductionArgument`, `DLMF.Elementary.trigReductionIndex`, `DLMF.Elementary.trigReductionAngle`, `DLMF.Elementary.arctanReductionStep`, and `DLMF.Elementary.arctanReductionSequence` ([source](DLMF/Elementary/Computation.lean#L27)) are exact scalings/iterations. They are recorded descriptively; the catalogue adds no numerical approximation implementation. The chosen integer indices, floor/nearest-integer conventions, and initial term of each recurrence matter.

  [DLMF 4.45.E1](https://dlmf.nist.gov/4.45.E1):
  The small logarithm argument obtained after `m` square roots.
  `DLMF.Elementary.logReductionArgument` ([definition](DLMF/Elementary/Computation.lean#L27)).

  [DLMF 4.45.E4](https://dlmf.nist.gov/4.45.E4):
  Nearest decimal scaling exponent for a real exponential argument.
  `DLMF.Elementary.expReductionIndex` ([definition](DLMF/Elementary/Computation.lean#L43)).

  [DLMF 4.45.E4](https://dlmf.nist.gov/4.45.E4):
  The reduced real exponential argument.
  `DLMF.Elementary.expReductionArgument` ([definition](DLMF/Elementary/Computation.lean#L47)).

  [DLMF 4.45.E6](https://dlmf.nist.gov/4.45.E6):
  Nearest half-turn index for a real trigonometric argument.
  `DLMF.Elementary.trigReductionIndex` ([definition](DLMF/Elementary/Computation.lean#L51)).

  [DLMF 4.45.E6](https://dlmf.nist.gov/4.45.E6):
  The reduced trigonometric angle, algebraically `π (x/π - m)`.
  `DLMF.Elementary.trigReductionAngle` ([definition](DLMF/Elementary/Computation.lean#L55)).

  [DLMF 4.45.E9](https://dlmf.nist.gov/4.45.E9):
  One stable half-angle reduction step for the arctangent.
  `DLMF.Elementary.arctanReductionStep` ([definition](DLMF/Elementary/Computation.lean#L90)).

  [DLMF 4.45.E9](https://dlmf.nist.gov/4.45.E9):
  The arctangent half-angle iteration starts at the original argument.
  `DLMF.Elementary.arctanReductionSequence` ([definition](DLMF/Elementary/Computation.lean#L94)).

## Chapter 5 — Gamma function

Expanded review: all 24 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§5.1–5.24 checked; the matching section is §5.2.

### §5.2 Definitions

<!-- retained entry 38 -->
- **Gamma**, [Euler integral 5.2.1 and continuation prose](https://dlmf.nist.gov/5.2.i):
  Mathlib `Complex.GammaIntegral` and `Complex.Gamma` in
  [Gamma/Basic](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L110),
  and `Real.Gamma`. `GammaIntegral` is the actual half-line integral;
  `Gamma` extends it by recurrence and is totalized to zero at poles.
  The reciprocal gamma is `1 / Complex.Gamma z`, not a separate local definition.

<!-- retained entry 39 -->
- **Psi/digamma**, [5.2.2](https://dlmf.nist.gov/5.2.E2): Mathlib
  `Complex.digamma = logDeriv Complex.Gamma` in
  [Digamma](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean#L48),
  and the independently defined real quotient `Real.digamma` in
  [Gamma/Digamma](DLMF/Gamma/Digamma.lean#L39).

<!-- retained entry 40 -->
- **Euler's constant**, [exact limit in 5.2.3](https://dlmf.nist.gov/5.2.E3):
  Mathlib `Real.eulerMascheroniConstant` in
  [EulerMascheroni](.lake/packages/mathlib/Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean).
  The accompanying decimal expansion is
  numerical and is excluded.

<!-- retained entry 41 -->
- **Pochhammer symbol/rising factorial**, [5.2.4–5](https://dlmf.nist.gov/5.2.E4):
  Mathlib `ascPochhammer` evaluated at the base, from
  [Polynomial/Pochhammer](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Pochhammer.lean);
  `DLMF.Hypergeometric.poch`
  is an abbreviation for this in [Hypergeometric/Basic](DLMF/Hypergeometric/Basic/Pochhammer.lean#L24).
  The gamma quotient is an identity away from poles, not its definition.

<!-- retained entry 42 -->
- **Falling factorial and Lah numbers**, [prose and 5.2.9](https://dlmf.nist.gov/5.2.E9):
  Mathlib `descPochhammer` in
  [Polynomial/Pochhammer](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Pochhammer.lean)
  and natural falling factorial `Nat.descFactorial` in
  [Factorial/Basic](.lake/packages/mathlib/Mathlib/Data/Nat/Factorial/Basic.lean#L332);
  `DLMF.Elementary.fallingPower` in
  [LogExpAnalysis](DLMF/Elementary/LogExpAnalysis.lean#L754) is the complex product.
  Lah numbers are expressible by the displayed binomial/factorial formula;
  no separately named Lah-number definition is used here.

### §5.7 Series Expansions

- **Reciprocal-Gamma Taylor coefficients and Binet integrand**, [DLMF 5.7.E1](https://dlmf.nist.gov/5.7.E1):
  cₖ of1/Γ is `DLMF.Gamma.recipGammaCoeff` ([source](DLMF/Gamma/SeriesExpansions.lean#L35)). The Binet integrandφ(t) in 5.9.2_5 is `DLMF.Gamma.binetPhi` ([source](DLMF/Gamma/IntegralRepresentations/HankelAndGaussian.lean#L82)). These exact auxiliary objects are distinct from decimal coefficient tables.

  [DLMF 5.7.E1](https://dlmf.nist.gov/5.7.E1):
  Taylor coefficients of `1/Γ` at zero, DLMF 5.7.1.
  `DLMF.Gamma.recipGammaCoeff` ([definition](DLMF/Gamma/SeriesExpansions.lean#L35)).

### §5.9 Integral Representations

- **Binet's integrand**, [DLMF 5.9.E2_5](https://dlmf.nist.gov/5.9.E2_5):
  Binet's integrand.
  `DLMF.Gamma.binetPhi` ([definition](DLMF/Gamma/IntegralRepresentations/HankelAndGaussian.lean#L82)).

### §5.10 Continued Fractions

- **Binet function and partially recorded continued-fraction coefficients**, [DLMF 5.10](https://dlmf.nist.gov/5.10):
  `DLMF.Gamma.logGammaBinet`, `DLMF.Gamma.logGammaContFractCoeff`, and `DLMF.Gamma.logGammaContinuedFraction` ([source](DLMF/Gamma/ContinuedFractions.lean#L29)) exist. The coefficient function contains only the seven displayed rational values and is zero thereafter: it is a finite truncation, not the full DLMF continued fraction. The corresponding convergence claim was already removed and the source records this limitation. The full coefficient sequence is a coverage gap.

  [DLMF 5.10.E1](https://dlmf.nist.gov/5.10.E1):
  Partial numerators `a_k` in DLMF 5.10.1, with the seven tabulated values.
  `DLMF.Gamma.logGammaContFractCoeff` ([definition](DLMF/Gamma/ContinuedFractions.lean#L29)).

  [DLMF 5.10.E1](https://dlmf.nist.gov/5.10.E1):
  The generalized continued fraction `0 + a₀/(z + a₁/(z + ⋯))` with the coefficients
  `logGammaContFractCoeff` of DLMF 5.10.1 (Stieltjes's continued fraction for Binet's function).
  `DLMF.Gamma.logGammaContinuedFraction` ([definition](DLMF/Gamma/ContinuedFractions.lean#L41)).

  [DLMF 5.10.E1](https://dlmf.nist.gov/5.10.E1):
  Binet's function, the left-hand side of 5.10.1.
  `DLMF.Gamma.logGammaBinet` ([definition](DLMF/Gamma/ContinuedFractions.lean#L48)).

### §5.11 Asymptotic Expansions

- **Scaled Gamma, Stirling coefficients and ratio coefficients**, [DLMF 5.11.E3](https://dlmf.nist.gov/5.11.E3):
  Γ*(z) is `DLMF.Gamma.scaledGamma`; its all-order coefficientsgₖ are `DLMF.Gamma.stirlingG`, and the ratio coefficients Gₖ(a,b) are `DLMF.Gamma.stirlingRatioG` ([source](DLMF/Gamma/Asymptotics/Stirling.lean#L36)). There are also separate `DLMF.Confluent.gammaScaled`, `DLMF.Confluent.gammaStirlingCoeff` implementations at their later use in §8.12. The recurrence-definedaₖ of 5.11.6, even shifted coefficients Hₖ(a,b) of 5.11.14, and scaled remainderR_K are formulas/coefficient expressions in the theorem statements; no additional independently named construction was identified. Exact coefficients/asymptotic expansions remain in scope.

  [DLMF 5.11.E3](https://dlmf.nist.gov/5.11.E3):
  Scaled Gamma `Γ*(z)` in DLMF 5.11.3.
  `DLMF.Gamma.scaledGamma` ([definition](DLMF/Gamma/Asymptotics/Stirling.lean#L36)).

  [DLMF 5.11.E4](https://dlmf.nist.gov/5.11.E4):
  Stirling coefficients, obtained by exponentiating the Bernoulli expansion
  of the logarithm of the scaled Gamma function. This recurrence specifies every order.
  `DLMF.Gamma.stirlingG` ([definition](DLMF/Gamma/Asymptotics/Stirling.lean#L503)).

  [DLMF 5.11.E15](https://dlmf.nist.gov/5.11.E15):
  Gamma-ratio coefficients, obtained by exponentiating the difference of
  Bernoulli-polynomial expansions of `log Γ(z+a)` and `log Γ(z+b)`.
  The recurrence defines all orders, including the higher coefficients needed in remainders.
  `DLMF.Gamma.stirlingRatioG` ([definition](DLMF/Gamma/Asymptotics/Stirling.lean#L755)).

### §5.14 Multidimensional Integrals

- **Simplex and Vandermonde product**, [DLMF 5.14](https://dlmf.nist.gov/5.14):
  Vₙ={t:tⱼ≥0,Σtⱼ≤1} is the real simplex domain used in the Gamma integral modules. Δ(t)=∏_{j<k}(tⱼ−tₖ) is `DLMF.Gamma.vandermonde` ([source](DLMF/Gamma/Multidimensional/SelbergLimits.lean#L32)). Its factor orientation must be kept when comparing Mathlib's Vandermonde APIs. Selberg and Dyson integrals are representations/evaluations of integrals on these domains, not new Gamma functions.

  [DLMF 5.14.E3](https://dlmf.nist.gov/5.14.E3):
  Vandermonde product, DLMF 5.14.3.
  `DLMF.Gamma.vandermonde` ([definition](DLMF/Gamma/Multidimensional/SelbergLimits.lean#L32)).

### §5.15 Polygamma Functions

- **Polygamma functions and Barnes G**, [DLMF 5.15](https://dlmf.nist.gov/5.15):
  `DLMF.Gamma.polygamma` ([source](DLMF/Gamma/Polygamma.lean#L36)) is the iterated complex derivative of digamma; the derivativesψ⁽ⁿ⁾ are the polygamma functions; the n=1,2,3,4 cases are trigamma, tetragamma, pentagamma and hexagamma. The special names are aliases within the same polygamma family. BarnesG, outside a Definitions heading, has independent constructions `DLMF.Gamma.barnesGTerm`, `DLMF.Gamma.barnesGSucc`, and `DLMF.Gamma.barnesG` ([source](DLMF/Gamma/BarnesG/WeierstrassProduct.lean#L35)), with G(z+1)=Γ(z)G(z),G(1)=1 and the entire product representation. The recurrence/normalization alone do not establish uniqueness.

### §5.17 Barnes’ G -Function (Double Gamma Function)

- **Barnes-G successor product**, [DLMF 5.17.E3](https://dlmf.nist.gov/5.17.E3):
  Barnes `G(z+1)` via the Weierstrass product.
  `DLMF.Gamma.barnesGSucc` ([definition](DLMF/Gamma/BarnesG/WeierstrassProduct.lean#L40)).

- **Glaisher–Kinkelin constant and q-Gamma/q-Beta**, [DLMF 5.17.E6](https://dlmf.nist.gov/5.17.E6):
  A=exp C is `DLMF.Gamma.glaisherKinkelin` ([source](DLMF/Gamma/BarnesG/WeierstrassProduct.lean#L639)); the exact limit and zeta-derivative representations are bridges, while its decimal display is excluded: numerical. In §5.18, the q-factorial and q-Beta are `DLMF.Gamma.qFactorial`, `DLMF.Gamma.qBeta` ([source](DLMF/Gamma/QGamma.lean#L34)), and the product q-Gamma is `DLMF.QSeries.qGamma` ([source](DLMF/QSeries/Basic/Pochhammer.lean#L39)). The q>1 formula uses reciprocal-base transformation; a construction confined to 0<q<1 is not automatically its continuation.

  [DLMF 5.17.E6](https://dlmf.nist.gov/5.17.E6):
  Glaisher–Kinkelin constant, via the first closed form for `C` in 5.17.7.
  `DLMF.Gamma.glaisherKinkelin` ([definition](DLMF/Gamma/BarnesG/WeierstrassProduct.lean#L639)).

### §5.18 q -Gamma and q -Beta Functions

- **Q-factorial, DLMF 5.18.2**, [DLMF 5.18.E2](https://dlmf.nist.gov/5.18.E2):
  q-factorial, DLMF 5.18.2.
  `DLMF.Gamma.qFactorial` ([definition](DLMF/Gamma/QGamma.lean#L34)).

- **Q Gamma**, [DLMF 5.18.E4](https://dlmf.nist.gov/5.18.E4):
  The `q`-gamma function (AAR §10.3):
  `Γ_q(x) = (q;q)_∞ / (q^x;q)_∞ · (1-q)^{1-x}`.
  `DLMF.QSeries.qGamma` ([definition](DLMF/QSeries/Basic/Pochhammer.lean#L39)).

- **Q-beta function, DLMF 5.18.11**, [DLMF 5.18.E11](https://dlmf.nist.gov/5.18.E11):
  q-beta function, DLMF 5.18.11.
  `DLMF.Gamma.qBeta` ([definition](DLMF/Gamma/QGamma.lean#L98)).

### §5.19 Mathematical Applications

- **Mellin–Barnes integral and sphere quantities**, [DLMF 5.19.ii](https://dlmf.nist.gov/5.19.ii):
  The prose defines Mellin–Barnes integrals as products/reciprocals of Gamma functions and a power, integrated on a doubly infinite contour eventually parallel to the imaginary axis. The project has concrete vertical-line and contour integrals, without one universal Mellin–Barnes special-function object. Sphere volume/surface expressions in §5.19(iii) use the ordinary Euclidean ball/sphere measures. Partition-function potentials/densities of §5.20 are application definitions without dedicated local constructions; numerical methods/tables/software add no new acquired functions.

## Chapter 6 — Exponential, logarithmic, sine and cosine integrals

Expanded review: all 21 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§6.1–6.21 checked; the matching section is §6.2.

All local names below, including names beginning `Real.`, are under
`DLMF.Confluent`.

### §6.2 Definitions and Interrelations

<!-- retained entry 43 -->
- **Principal exponential integral E₁**, [6.2.1–2](https://dlmf.nist.gov/6.2.E1):
  `genExpIntE 1 z` in [ExpIntegral](DLMF/Confluent/Basic/ExponentialIntegrals.lean#L25);
  `genExpIntEOnLog 1 w` retains arbitrary sheets. These are incomplete-gamma
  constructions; the horizontal-ray and half-line integrals are bridge theorems.

<!-- retained entry 44 -->
- **Entire complementary exponential integral Ein**, [6.2.3](https://dlmf.nist.gov/6.2.E3):
  series `expIntEin` in [ExpIntegrals/Basic](DLMF/ExpIntegrals/Basic/Functions.lean#L25)
  and independent real interval integral `Real.expIntEin` in
  [ExpIntegral](DLMF/Confluent/Basic/ExponentialIntegrals.lean#L30).

<!-- retained entry 45 -->
- **Real Ei and logarithmic integral li**, [6.2.5–8](https://dlmf.nist.gov/6.2.E5):
  `Real.expIntEi` and `Real.logIntLi` in
  [ExpIntegrals/Basic](DLMF/ExpIntegrals/Basic/Functions.lean#L60), using the continued
  series and `Ei(log x)`. The principal-value integrals are theorem characterizations,
  not separate functions. DLMF excludes `Ei(0)` and restricts this li definition
  to `x > 1`.

<!-- retained entry 46 -->
- **Sine integral Si and shifted si**, [6.2.9–10](https://dlmf.nist.gov/6.2.E9):
  complex series `sinInt` and shift `sinIntTail` in
  [ExpIntegrals/Basic](DLMF/ExpIntegrals/Basic/Functions.lean#L30);
  independent real interval-integral `Real.sinInt` in
  [ExpIntegral](DLMF/Confluent/Basic/ExponentialIntegrals.lean#L35).

<!-- retained entry 47 -->
- **Cosine integral Ci and entire Cin**, [6.2.11–13](https://dlmf.nist.gov/6.2.E11):
  `cosIntCin`, `cosInt` in [ExpIntegrals/Basic](DLMF/ExpIntegrals/Basic/Functions.lean#L35),
  and the real integral/logarithm constructions `Real.cosIntCin`, `Real.cosInt`
  in [ExpIntegral](DLMF/Confluent/Basic/ExponentialIntegrals.lean#L40).
  Complex Ci uses the principal logarithm; it does not encode both banks as a set.

<!-- retained entry 48 -->
- **Hyperbolic integrals Shi and Chi**, [6.2.15–16](https://dlmf.nist.gov/6.2.E15):
  `sinhInt` and `coshInt` in [ExpIntegrals/Basic](DLMF/ExpIntegrals/Basic/Functions.lean#L50),
  respectively an entire series and a principal-logarithm-plus-series definition.

<!-- retained entry 49 -->
- **Auxiliary f and g**, [6.2.17–18](https://dlmf.nist.gov/6.2.E17):
  `expIntAuxF` and `expIntAuxG` in
  [ExpIntegrals/Basic](DLMF/ExpIntegrals/Basic/Functions.lean#L70).

### §6.4 Analytic Continuation

- **Logarithmic-plane exponential integral and series coefficients**, [DLMF 6.4.E1](https://dlmf.nist.gov/6.4.E1):
  `DLMF.Confluent.expIntE1OnLog` ([source](DLMF/ExpIntegrals/Continuation.lean#L24)) records E₁ with an explicit logarithmic argument, preserving monodromy. The reciprocal-factorial and spherical-Bessel coefficients of §6.10 are `DLMF.Confluent.expIntReciprocalFactorialCoeff`, `DLMF.Confluent.expIntSphericalCoeff` ([source](DLMF/ExpIntegrals/Expansions.lean#L79)). Their recurrence/initial conventions differ from arbitrary coefficients of an expansion with the same limiting order.

  [DLMF 6.4.E1](https://dlmf.nist.gov/6.4.E1):
  E₁ on the logarithmic plane.
  `DLMF.Confluent.expIntE1OnLog` ([definition](DLMF/ExpIntegrals/Continuation.lean#L24)).

### §6.10 Other Series Expansions

- **Reciprocal factorial coefficients, with the recurrence of DLMF 6.10.3**, [DLMF 6.10.E3](https://dlmf.nist.gov/6.10.E3):
  Reciprocal factorial coefficients, with the recurrence of DLMF 6.10.3.
  `DLMF.Confluent.expIntReciprocalFactorialCoeff` ([definition](DLMF/ExpIntegrals/Expansions.lean#L79)).

- **Spherical-Bessel expansion coefficients**, [DLMF 6.10.E7](https://dlmf.nist.gov/6.10.E7):
  Spherical-Bessel expansion coefficients.
  `DLMF.Confluent.expIntSphericalCoeff` ([definition](DLMF/ExpIntegrals/Expansions.lean#L538)).

### §6.12 Asymptotic Expansions

- **Auxiliary remainders, ordered zeros and Acton integrals**, [DLMF 6.12.E5](https://dlmf.nist.gov/6.12.E5):
  Rₙ^(f),Rₙ^(g) are the finite auxiliary-function remainders `DLMF.Confluent.expIntAsymptoticRemainder` ([source](DLMF/ExpIntegrals/Asymptotics.lean#L28)). The real Ei zero is `DLMF.Confluent.Real.expIntEiZero` ([source](DLMF/ExpIntegrals/ZerosIntegrals.lean#L27)); the Ci/si positive zeros in §6.13 are `DLMF.Confluent.Real.cosIntZero` and `DLMF.Confluent.Real.sinIntTailZero`. The ActonAₙ,Bₙ,Cₙ integrals introduced in §6.18.1 have actual `DLMF.Confluent.expIntActonA`, `DLMF.Confluent.expIntActonB`, `DLMF.Confluent.expIntActonC` definitions ([source](DLMF/ExpIntegrals/ZerosIntegrals.lean#L687)). Decimal zero approximations are excluded, while exact zero selection and asymptotics remain in scope.

  [DLMF 6.12.E5](https://dlmf.nist.gov/6.12.E5):
  Finite auxiliary-function remainder.
  `DLMF.Confluent.expIntAsymptoticRemainder` ([definition](DLMF/ExpIntegrals/Asymptotics.lean#L28)).

### §6.13 Zeros

- **Unique real zero of Ei**, [DLMF 6.13.E1](https://dlmf.nist.gov/6.13.E1):
  The unique real zero of Ei.
  `DLMF.Confluent.Real.expIntEiZero` ([definition](DLMF/ExpIntegrals/ZerosIntegrals.lean#L27)).

### §6.16 Mathematical Applications

- **Fourier partial sum and Gibbs phenomenon**, [DLMF 6.16.i](https://dlmf.nist.gov/6.16.i):
  The displayed Sₙ and x-dependent auxiliaryβ are finite-sum/rescaling expressions illustrating nonuniform convergence at a jump. No separately named local Gibbs constant or new sine-integral function is defined. The percentages/decimal overshoot descriptions are excluded: numerical.

### §6.18 Methods of Computation

- **Acton auxiliary integrals A, B and C**, [DLMF 6.18.E1](https://dlmf.nist.gov/6.18.E1):
  Acton auxiliary integral.
  `DLMF.Confluent.expIntActonA` ([definition](DLMF/ExpIntegrals/ZerosIntegrals.lean#L687)).

  [DLMF 6.18.E1](https://dlmf.nist.gov/6.18.E1):
  Acton auxiliary integral.
  `DLMF.Confluent.expIntActonB` ([definition](DLMF/ExpIntegrals/ZerosIntegrals.lean#L692)).

  [DLMF 6.18.E1](https://dlmf.nist.gov/6.18.E1):
  Acton auxiliary integral.
  `DLMF.Confluent.expIntActonC` ([definition](DLMF/ExpIntegrals/ZerosIntegrals.lean#L697)).

## Chapter 7 — Error functions, Dawson's and Fresnel integrals

Expanded review: all 25 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§7.1–7.25 checked; matching headings are §7.2, §7.18(i),
and §7.19(i).

The local complex functions in this section are in namespace `DLMF.Confluent`.

### §7.2 Definitions

<!-- retained entry 50 -->
- **erf and erfc**, [7.2.1–2](https://dlmf.nist.gov/7.2.E1):
  `erf` and `erfc` in [Confluent/Basic](DLMF/Confluent/Basic/ErrorFunctions.lean#L27)
  use the Kummer series and its complement. Independent real interval-integral
  definitions are `TauCeti.Real.erf` and `TauCeti.Real.erfc` in
  [TauCeti/Erf](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/Erf.lean#L62);
  local `erf_ofReal` and `erfc_ofReal` are bridges.
  The independent real integral `DLMF.Confluent.Real.generalizedErrorIntegral 2`
  in [InverseGeneralized](DLMF/ErrorFunctions/InverseGeneralized.lean#L25)
  differs by the factor 2/√π. The §7.1 notation variants `scaledErf`,
  `gaussianCdf`, `gaussianTail` in
  [Basic](DLMF/ErrorFunctions/Basic/Functions.lean#L64) are argument/normalization
  wrappers, not new integral constructions.

<!-- retained entry 51 -->
- **Faddeeva/probability function w**, [7.2.3](https://dlmf.nist.gov/7.2.E3):
  `faddeevaW` in [ErrorFunctions/Basic](DLMF/ErrorFunctions/Basic/Functions.lean#L24).

<!-- retained entry 52 -->
- **Dawson F**, [7.2.5](https://dlmf.nist.gov/7.2.E5):
  `dawsonF` in [ErrorFunctions/Basic](DLMF/ErrorFunctions/Basic/Functions.lean#L29),
  using a straight-segment primitive. `dawsonPrimitive` is the corresponding
  unscaled primitive in the same file.
  `DLMF.Confluent.Real.generalizedDawsonIntegral 2` in
  [InverseGeneralized](DLMF/ErrorFunctions/InverseGeneralized.lean#L29)
  is an independent real integral of exp(t²); multiplying it by exp(−x²)
  gives Dawson's normalization.

- **Independent real Dawson integral**, [DLMF 7.2.E5](https://dlmf.nist.gov/7.2.E5):
  `DLMF.Confluent.Real.dawsonF` ([source](DLMF/Confluent/Basic/ErrorFunctions.lean#L45)) directly defines exp(−x²) times the real interval integral of exp(t²). It is a separate real integral construction from the entire straight-segment definition and from the unscaled generalized Dawson integral.

<!-- retained entry 53 -->
- **Fresnel tail, C and S**, [7.2.6–8](https://dlmf.nist.gov/7.2.E6):
  `fresnelTail`, `fresnelCosInt`, `fresnelSinInt` in
  [ErrorFunctions/Basic](DLMF/ErrorFunctions/Basic/Functions.lean#L34).
  C and S use the DLMF phase `πt²/2`; the tail is its entire continued
  expression `(1+i)/2 - C - iS`. The rescaled `fresnelC1`, `fresnelS1`,
  `fresnelC2`, `fresnelS2` in the same file are different argument normalizations.

- **Independent real Fresnel integrals**, [DLMF 7.2.E7](https://dlmf.nist.gov/7.2.E7) and [7.2.E8](https://dlmf.nist.gov/7.2.E8):
  `DLMF.Confluent.Real.fresnelCosInt` and `DLMF.Confluent.Real.fresnelSinInt` ([source](DLMF/Confluent/Basic/ErrorFunctions.lean#L37)) are real interval integrals of cos(πt²/2) and sin(πt²/2). These are independent integral definitions of the real restrictions, with the same DLMF phase, rather than wrappers evaluating the complex primitives.

<!-- retained entry 54 -->
- **Fresnel auxiliary f and g**, [7.2.10–11](https://dlmf.nist.gov/7.2.E10):
  `fresnelAuxFComplex` and `fresnelAuxGComplex` in
  [ErrorFunctions/Basic](DLMF/ErrorFunctions/Basic/Functions.lean#L49).

- **Real Fresnel auxiliary function f**, [DLMF 7.2.E10](https://dlmf.nist.gov/7.2.E10):
  The auxiliary Fresnel function `f(x) = (1/2 - S(x)) cos(πx²/2) - (1/2 - C(x)) sin(πx²/2)`
  (DLMF 7.2.10).
  `DLMF.Confluent.fresnelAuxF` ([definition](DLMF/Confluent/Basic/ErrorFunctions.lean#L49)).

- **Real Fresnel auxiliary function g**, [DLMF 7.2.E11](https://dlmf.nist.gov/7.2.E11):
  The auxiliary Fresnel function `g(x) = (1/2 - C(x)) cos(πx²/2) + (1/2 - S(x)) sin(πx²/2)`
  (DLMF 7.2.11).
  `DLMF.Confluent.fresnelAuxG` ([definition](DLMF/Confluent/Basic/ErrorFunctions.lean#L56)).

<!-- retained entry 55 -->
- **Goodwin–Staton integral**, [7.2.12](https://dlmf.nist.gov/7.2.E12):
  `goodwinStatonG` in [ErrorFunctions/Basic](DLMF/ErrorFunctions/Basic/Functions.lean#L59),
  an actual half-line integral, interpreted on the slit plane.

### §7.5 Interrelations

- **Signed Fresnel-to-Gaussian change of variable**, [DLMF 7.5.E7](https://dlmf.nist.gov/7.5.E7):
  Signed Fresnel-to-Gaussian change of variable.
  `DLMF.Confluent.fresnelZetaComplex` ([definition](DLMF/ErrorFunctions/Relations.lean#L213)).

### §7.8 Inequalities

- **Mills ratio, zero families and Fresnel rescaling**, [DLMF 7.8.E1](https://dlmf.nist.gov/7.8.E1):
  `DLMF.Confluent.Real.millsRatio` ([source](DLMF/ErrorFunctions/BoundsAsymptotics/ContinuedFractions.lean#L29)) uses the DLMF e^(x²)∫ₓ∞e^(−t²)dt normalization, differing from some statistics conventions. The selected error/Fresnel zero families andλ,μ,α scales are `DLMF.Confluent.errorFunctionZero`, `DLMF.Confluent.fresnelFunctionZero`, `DLMF.Confluent.errorZeroLambda`, `DLMF.Confluent.errorZeroMu`, `DLMF.Confluent.fresnelZeroLambda`, `DLMF.Confluent.fresnelZeroAlpha` ([source](DLMF/ErrorFunctions/Zeros.lean#L31)); the qualifications shown retain the namespaces of the actual definitions. The signed Gaussian/Fresnel variable of 7.5.7 is also an actual `DLMF.Confluent.fresnelZetaComplex` construction.

  [DLMF 7.8.E1](https://dlmf.nist.gov/7.8.E1):
  Mills ratio in DLMF normalization.
  `DLMF.Confluent.Real.millsRatio` ([definition](DLMF/ErrorFunctions/BoundsAsymptotics/ContinuedFractions.lean#L29)).

### §7.12 Asymptotic Expansions

- **Finite Fresnel auxiliary remainder**, [DLMF 7.12.E4](https://dlmf.nist.gov/7.12.E4):
  Finite Fresnel auxiliary remainder.
  `DLMF.Confluent.fresnelAsymptoticRemainder` ([definition](DLMF/ErrorFunctions/BoundsAsymptotics/FresnelRemainders.lean#L32)).

### §7.13 Zeros

- **Error-function zero scales λ and μ**, [DLMF 7.13.E2](https://dlmf.nist.gov/7.13.E2):
  Large error-function zero variable λ.
  `DLMF.Confluent.errorZeroLambda` ([definition](DLMF/ErrorFunctions/Zeros.lean#L293)).

  [DLMF 7.13.E2](https://dlmf.nist.gov/7.13.E2):
  Logarithmic error-function zero variable μ.
  `DLMF.Confluent.errorZeroMu` ([definition](DLMF/ErrorFunctions/Zeros.lean#L298)).

- **Fresnel zero scales λ and α**, [DLMF 7.13.E6](https://dlmf.nist.gov/7.13.E6):
  Fresnel zero variable λ.
  `DLMF.Confluent.fresnelZeroLambda` ([definition](DLMF/ErrorFunctions/Zeros.lean#L309)).

  [DLMF 7.13.E6](https://dlmf.nist.gov/7.13.E6):
  Fresnel zero logarithmic variable α.
  `DLMF.Confluent.fresnelZeroAlpha` ([definition](DLMF/ErrorFunctions/Zeros.lean#L314)).

### §7.16 Generalized Error Functions

- **Generalized unscaled error and Dawson integrals**, [DLMF 7.16](https://dlmf.nist.gov/7.16):
  ∫₀ˣexp(−tᵖ)dt and∫₀ˣexp(tᵖ)dt are `DLMF.Confluent.Real.generalizedErrorIntegral`, `DLMF.Confluent.Real.generalizedDawsonIntegral` ([source](DLMF/ErrorFunctions/InverseGeneralized.lean#L25)). The latter is unscaled; it is not e^(−xᵖ) times that integral. Both are real constructions, with p,x domain hypotheses on their incomplete-Gamma bridges.

### §7.17 Inverse Error Functions

<!-- retained entry 56 -->
- **Inverse erf and erfc**, [7.17.1](https://dlmf.nist.gov/7.17.E1):
  upstream `_root_.Real.erfInv` in
  [TauCeti/Erf](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/Erf.lean#L251)
  is the inverse order isomorphism of `TauCeti.Real.erf`, with zero outside
  (−1,1). `DLMF.Confluent.Real.invErf` is a wrapper around it;
  `DLMF.Confluent.Real.invErfc x = Real.invErf (1-x)` in
  [InverseGeneralized](DLMF/ErrorFunctions/InverseGeneralized.lean#L172)
  has the corresponding intended domain (0,2). No complex inverse branch
  is selected by these real functions. The complementary wrapper is `DLMF.Confluent.Real.invErfc`.

- **Inverse-error coefficients and transition variables**, [DLMF 7.17.ii](https://dlmf.nist.gov/7.17.ii):
  In addition to the retained inverse functions, `DLMF.Confluent.invErfSeriesCoeff`, `DLMF.Confluent.invErfDerivativePoly`, `DLMF.Confluent.invErfTaylorCoeff` ([source](DLMF/ErrorFunctions/InverseGeneralized.lean#L198)) record recursive coefficients, derivative polynomials, and derivative-defined Taylor coefficients. The asymptoticu,v of 7.17.5–6 are `DLMF.Confluent.invErfcAsymptoticU`, `DLMF.Confluent.invErfcAsymptoticV`. Equality of recursive and analytic coefficients is a theorem, not an alias.

  [DLMF 7.17.E5](https://dlmf.nist.gov/7.17.E5):
  Small-argument inverse-erfc variable u.
  `DLMF.Confluent.invErfcAsymptoticU` ([definition](DLMF/ErrorFunctions/InverseGeneralized.lean#L602)).

  [DLMF 7.17.E6](https://dlmf.nist.gov/7.17.E6):
  Small-argument inverse-erfc logarithmic variable v.
  `DLMF.Confluent.invErfcAsymptoticV` ([definition](DLMF/ErrorFunctions/InverseGeneralized.lean#L607)).

### §7.18 Repeated Integrals of the Complementary Error Function

<!-- retained entry 57 -->
- **Repeated complementary error integrals**, [7.18.1–2](https://dlmf.nist.gov/7.18.E1):
  `DLMF.Confluent.iteratedErfc` in
  [Repeated](DLMF/ErrorFunctions/Repeated.lean#L26), with integer index `n ≥ -1`.
  It handles `-1` as the Gaussian and nonnegative indices by a shifted
  half-line integral; indices below `-1` are artificial zero values.
  `gaussianProbabilityHh` in the same file is a related independent Gaussian
  moment normalization, with exponent `-(z+t)²/2`.

### §7.19 Voigt Functions

<!-- retained entry 58 -->
- **Voigt U, V, and line-broadening H**, [7.19.1–4](https://dlmf.nist.gov/7.19.E1):
  `DLMF.Confluent.Real.voigtU`, `voigtV`, and `voigtH` in
  [Voigt](DLMF/ErrorFunctions/Voigt.lean#L23).
  These are actual real whole-line integrals. Their mathematical domains are
  `t > 0` and `a > 0`; 7.19.3 is a complex-erfc bridge, not a fourth definition. The fully qualified remaining names are `DLMF.Confluent.Real.voigtV` and `DLMF.Confluent.Real.voigtH`.

### §7.20 Mathematical Applications

- **Cornu spiral and Gaussian distribution function**, [DLMF 7.20.ii](https://dlmf.nist.gov/7.20.ii):
  Cornu's spiral is the curve x=C(t),y=S(t) (the 3-dimensional corkscrew also hasz=t). No independently named local curve was found; the Fresnel coordinate functions already exist. The normal CDFP(x) with meanμ and standard deviationσ is an affine-error-function expression; Mathlib's Gaussian measure/CDF provides the probability-theory counterpart, with varianceσ² andσ>0. Voigt convolution and the alternate plasma-dispersion name in §7.21 reuse existing functions.

## Chapter 8 — Incomplete gamma and related functions

Expanded review: all 28 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§8.1–8.28 checked; matching headings are §8.2 (including (i)),
§8.17(i)/(vii), §8.19(i), and §8.21(i)/(ii). Nested matching headings are counted
once when discussing their mathematical content.

### §8.2 Definitions and Basic Properties

<!-- retained entry 59 -->
- **Lower incomplete gamma**, [8.2.1](https://dlmf.nist.gov/8.2.E1):
  `DLMF.Confluent.lowerIncGamma` in
  [Confluent/Basic](DLMF/Confluent/Basic/IncompleteGamma.lean#L22), using a Kummer series;
  `lowerIncGammaOnLog` in [IncompleteGamma/Basic](DLMF/IncompleteGamma/Basic.lean#L30)
  retains the logarithmic sheet. `TauCeti.lowerIncompleteGamma` in
  [TauCeti/IncompleteGamma](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/IncompleteGamma.lean#L115)
  is an independent real integral for positive shape and nonnegative endpoint;
  it truncates negative endpoints to zero and assigns zero for nonpositive shape.
  At nonpositive integral parameters, the
  ordinary local formula has totalized values rather than pole data.

<!-- retained entry 60 -->
- **Upper incomplete gamma**, [8.2.2](https://dlmf.nist.gov/8.2.E2):
  `DLMF.Confluent.upperIncGamma` in
  [Confluent/Relations](DLMF/Confluent/Basic/IncompleteGamma.lean#L27), using Tricomi U;
  `upperIncGammaOnLog` in [IncompleteGamma/Basic](DLMF/IncompleteGamma/Basic.lean#L26)
  continues on the logarithmic plane, also at integral parameters. Integral
  representations are bridge theorems, not additional functions.

<!-- retained entry 61 -->
- **Normalized P and Q**, [8.2.4](https://dlmf.nist.gov/8.2.E4):
  quotient definitions `DLMF.Statistical.normIncGammaP`, `normIncGammaQ` in
  [Statistical/IncompleteGamma](DLMF/Statistical/Basic/IncompleteGamma.lean#L26);
  parameter-continuation definitions `DLMF.Confluent.normIncGammaPContinued`,
  `normIncGammaQContinued`, `normIncGammaPOnLog`, `normIncGammaQOnLog` in
  [IncompleteGamma/Basic](DLMF/IncompleteGamma/Basic.lean#L34).
  The continued functions are materially different at nonpositive integral
  parameters. `TauCeti.regularizedGamma` is the real integral quotient
  representing P for positive real shape; `1 - regularizedGamma` represents Q
  on that domain without another definition.

<!-- retained entry 62 -->
- **Tricomi's entire γ-star**, [8.2.6–7](https://dlmf.nist.gov/8.2.E6):
  `DLMF.Statistical.scIncGamma` in
  [Statistical/IncompleteGamma](DLMF/Statistical/Basic/IncompleteGamma.lean#L35),
  using the regularized confluent series rather than the singular quotient.

### §8.4 Special Values

- **Exponential partial sums and incomplete-Gamma inequality auxiliaries**, [DLMF 8.4.E11](https://dlmf.nist.gov/8.4.E11):
  eₙ(z) is `DLMF.Confluent.expPartialSum` ([source](DLMF/IncompleteGamma/SpecialValues.lean#L27)), another actual construction alongside §4.9's polynomial. The bounds of §8.10 introduceϑ,c_a,d_a,α_a,β_a, represented by `DLMF.Confluent.Real.upperGammaTheta`, `DLMF.Confluent.Real.upperGammaCa`, `DLMF.Confluent.Real.upperGammaDa`, `DLMF.Confluent.Real.gammaPAlpha`, `DLMF.Confluent.Real.gammaPBeta` ([source](DLMF/IncompleteGamma/BoundsFractions.lean#L113)). The displayed rationalA₁,B₁,A₂,B₂ andI=∫₀ˣt^(a−1)eᵗdt are expressions in inequalities; they are not substitute definitions of incomplete Gamma. The local constants include their continuous a=1 values.

  [DLMF 8.4.E11](https://dlmf.nist.gov/8.4.E11):
  The finite exponential sum e_n.
  `DLMF.Confluent.expPartialSum` ([definition](DLMF/IncompleteGamma/SpecialValues.lean#L27)).

### §8.10 Inequalities

- **First-order real incomplete-Gamma remainder ratio**, [DLMF 8.10.E3](https://dlmf.nist.gov/8.10.E3):
  The first-order real incomplete-Gamma remainder ratio.
  `DLMF.Confluent.Real.upperGammaTheta` ([definition](DLMF/IncompleteGamma/BoundsFractions.lean#L113)).

- **Incomplete-Gamma inequality constants cₐ and dₐ**, [DLMF 8.10.E9](https://dlmf.nist.gov/8.10.E9):
  Constant c_a.
  `DLMF.Confluent.Real.upperGammaCa` ([definition](DLMF/IncompleteGamma/BoundsFractions.lean#L463)).

  [DLMF 8.10.E9](https://dlmf.nist.gov/8.10.E9):
  Constant d_a.
  `DLMF.Confluent.Real.upperGammaDa` ([definition](DLMF/IncompleteGamma/BoundsFractions.lean#L468)).

- **Lower and upper incomplete-Gamma bounding constants**, [DLMF 8.10.E12](https://dlmf.nist.gov/8.10.E12):
  Lower bounding constant α_a, with its continuous value at a=1.
  `DLMF.Confluent.Real.gammaPAlpha` ([definition](DLMF/IncompleteGamma/BoundsFractions.lean#L537)).

  [DLMF 8.10.E12](https://dlmf.nist.gov/8.10.E12):
  Upper bounding constant β_a.
  `DLMF.Confluent.Real.gammaPBeta` ([definition](DLMF/IncompleteGamma/BoundsFractions.lean#L542)).

### §8.11 Asymptotic Approximations and Expansions

- **Large-argument and exponential-partial-sum coefficients**, [DLMF 8.11.E1](https://dlmf.nist.gov/8.11.E1):
  uₖ and Rₙ are `DLMF.Confluent.incGammaAsymptoticCoeff`, `DLMF.Confluent.incGammaAsymptoticRemainder`; bₖ(λ) is `DLMF.Confluent.incGammaLambdaPolynomial` ([source](DLMF/IncompleteGamma/Asymptotics/LargeArgument.lean#L35)). Sₙ(x) and dₖ(x) are `DLMF.Confluent.expPartialSumRemainderS`, `DLMF.Confluent.expPartialSumRemainderCoeff` ([source](DLMF/IncompleteGamma/Asymptotics/PartialSums.lean#L387)). The remainders preserve logarithmic-plane arguments where needed. These exact coefficients and asymptotic families are mathematical definitions, rather than numerical approximants.

  [DLMF 8.11.E1](https://dlmf.nist.gov/8.11.E1):
  Falling-factorial incomplete-Gamma coefficients.
  `DLMF.Confluent.incGammaAsymptoticCoeff` ([definition](DLMF/IncompleteGamma/Asymptotics/LargeArgument.lean#L35)).

  [DLMF 8.11.E2](https://dlmf.nist.gov/8.11.E2):
  Normalized finite upper-Gamma remainder on the logarithmic plane.
  `DLMF.Confluent.incGammaAsymptoticRemainder` ([definition](DLMF/IncompleteGamma/Asymptotics/LargeArgument.lean#L40)).

  [DLMF 8.11.E9](https://dlmf.nist.gov/8.11.E9):
  Polynomials b_k(lam), defined by the differential recurrence 8.11.9.
  `DLMF.Confluent.incGammaLambdaPolynomial` ([definition](DLMF/IncompleteGamma/Asymptotics/LargeArgument.lean#L381)).

  [DLMF 8.11.E15](https://dlmf.nist.gov/8.11.E15):
  The exponential partial-sum remainder S_n.
  `DLMF.Confluent.expPartialSumRemainderS` ([definition](DLMF/IncompleteGamma/Asymptotics/PartialSums.lean#L387)).

  [DLMF 8.11.E19](https://dlmf.nist.gov/8.11.E19):
  The coefficients d_k(x).
  `DLMF.Confluent.expPartialSumRemainderCoeff` ([definition](DLMF/IncompleteGamma/Asymptotics/PartialSums.lean#L1089)).

### §8.12 Uniform Asymptotic Expansions for Large Parameter

- **Uniform-Gamma transition variables and all-order coefficients**, [DLMF 8.12.E1](https://dlmf.nist.gov/8.12.E1):
  λ=z/a,η²/2=λ−1−logλ with η~λ−1; `DLMF.Confluent.gammaUniformEtaOnLog` uses an explicit log coordinate and `DLMF.Confluent.gammaEtaFactor`. Both remainder functions `DLMF.Confluent.gammaUniformS` and `DLMF.Confluent.gammaUniformT` exist, together with `DLMF.Confluent.gammaUniformC`, inverse log map `DLMF.Confluent.gammaUniformInverseLog`, inverse-series `DLMF.Confluent.gammaUniformAlpha`, and Taylor coefficients `DLMF.Confluent.gammaUniformD` ([source](DLMF/IncompleteGamma/UniformAsymptotics.lean#L42)). `DLMF.Confluent.gammaUniformFilter` is the corresponding uniform-domain filter. Some analytic/removable-value specifications remain admitted; the existence of these definitions does not establish all their intended analytic properties.

  [DLMF 8.12.E1](https://dlmf.nist.gov/8.12.E1):
  η on the logarithmic λ-plane, normalized by η~log λ~λ-1 at λ=1.
  `DLMF.Confluent.gammaUniformEtaOnLog` ([definition](DLMF/IncompleteGamma/UniformAsymptotics.lean#L46)).

  [DLMF 8.12.E4](https://dlmf.nist.gov/8.12.E4):
  The exact S remainder, with w the logarithm of λ.
  `DLMF.Confluent.gammaUniformS` ([definition](DLMF/IncompleteGamma/UniformAsymptotics.lean#L302)).

  [DLMF 8.12.E9](https://dlmf.nist.gov/8.12.E9):
  Uniform coefficients, with removable singularities filled by limits at w=0.
  `DLMF.Confluent.gammaUniformC` ([definition](DLMF/IncompleteGamma/UniformAsymptotics.lean#L431)).

- **Paris transition coefficients and incomplete-Gamma inverse**, [DLMF 8.12.E18](https://dlmf.nist.gov/8.12.E18):
  χ=(z−a)/√z andd(χ) are represented by expressions and `DLMF.Confluent.gammaParisD`; both familiesAₖ,Bₖ have actual `DLMF.Confluent.gammaParisRawCoeff`, `DLMF.Confluent.gammaParisA`, `DLMF.Confluent.gammaParisB` constructions ([source](DLMF/IncompleteGamma/UniformAsymptotics.lean#L986)). They are extracted through asymptotic coefficients, with identifying statements still admitted. The inverse Q is `DLMF.Confluent.gammaQInverse`, valued in ℝ≥0∞ so that q=0 maps to ∞ andq=1 to 0; its interior is an existence-based selected solution, requiring its specification theorem.

  [DLMF 8.12.E19](https://dlmf.nist.gov/8.12.E19):
  The parabolic transition function d(χ).
  `DLMF.Confluent.gammaParisD` ([definition](DLMF/IncompleteGamma/UniformAsymptotics.lean#L986)).

  [DLMF 8.12.E21](https://dlmf.nist.gov/8.12.E21):
  The inverse Q, including x=∞ at q=0.
  `DLMF.Confluent.gammaQInverse` ([definition](DLMF/IncompleteGamma/UniformAsymptotics.lean#L1016)).

### §8.17 Incomplete Beta Functions

<!-- retained entry 63 -->
- **Incomplete beta Bₓ**, [8.17.1](https://dlmf.nist.gov/8.17.E1):
  `DLMF.Statistical.Real.incBeta` in
  [Statistical/IncompleteBeta](DLMF/Statistical/IncompleteBeta.lean#L49)
  is an interval integral with real endpoint and complex parameters;
  `DLMF.Statistical.incBeta` in
  [IncompleteGamma/Beta](DLMF/IncompleteGamma/Beta.lean#L26) is a principal
  hypergeometric continuation, with a separate value at `z = 1`.

<!-- retained entry 64 -->
- **Normalized incomplete beta Iₓ**, [8.17.2](https://dlmf.nist.gov/8.17.E2):
  `DLMF.Statistical.Real.normIncBetaI` is the integral quotient;
  `DLMF.Statistical.normIncBetaI` is the continued regularized formula in
  [IncompleteGamma/Beta](DLMF/IncompleteGamma/Beta.lean#L30), preserving
  a removable `a = 0` specialization. They should not be identified at
  exceptional parameters merely by totalized division.

<!-- retained entry 65 -->
- **Complete beta**, [8.17.3](https://dlmf.nist.gov/8.17.E3): Mathlib
  `Complex.betaIntegral` in
  [Gamma/Beta](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L60).
  The gamma quotient is a bridge on its proper parameter domain. The addendum
  [8.17.24](https://dlmf.nist.gov/8.17.E24) is a series identity for I, not a new definition.

- **Incomplete-Beta recurrence and asymptotic parameters**, [DLMF 8.17.E11](https://dlmf.nist.gov/8.17.E11):
  x′=1−x,c=a+b−1 and the continued-fractiondₖ are `DLMF.Statistical.incBetaComplement`, `DLMF.Statistical.incBetaContiguousParameter`, `DLMF.Statistical.incBetaFractionD` ([source](DLMF/IncompleteGamma/Beta.lean#L224)). The §8.18 constructions include `DLMF.Statistical.Real.betaXi`, `DLMF.Statistical.Real.betaGeneratingKernel`, `DLMF.Statistical.Real.betaGeneratingCoeff`, `DLMF.Statistical.betaAuxF`, `DLMF.Statistical.Real.betaCenter`, `DLMF.Statistical.Real.betaEta`, `DLMF.Statistical.Real.betaEtaInverse`, `DLMF.Statistical.betaSymmetricC`, `DLMF.Statistical.Real.betaZeta`, `DLMF.Statistical.Real.betaGeneralX`, `DLMF.Statistical.betaGeneralH`, and `DLMF.Statistical.Real.incBetaInverse` ([source](DLMF/IncompleteGamma/BetaAsymptotics.lean#L240)). These give the endpoint variable, generating series, Fₖ sequence, signed transition variables and inverse maps, and both coefficient familiescₖ,hₖ. The branches at x=x₀ are filled by specified limiting conventions, not arbitrary principal square roots.

  [DLMF 8.17.E11](https://dlmf.nist.gov/8.17.E11):
  The complementary argument x prime.
  `DLMF.Statistical.incBetaComplement` ([definition](DLMF/IncompleteGamma/Beta.lean#L224)).

  [DLMF 8.17.E11](https://dlmf.nist.gov/8.17.E11):
  The parameter c of the contiguous recurrences.
  `DLMF.Statistical.incBetaContiguousParameter` ([definition](DLMF/IncompleteGamma/Beta.lean#L229)).

  [DLMF 8.17.E23](https://dlmf.nist.gov/8.17.E23):
  The Gauss continued-fraction numerators d_k.
  `DLMF.Statistical.incBetaFractionD` ([definition](DLMF/IncompleteGamma/Beta.lean#L599)).

### §8.18 Asymptotic Expansions of I x ⁡ ( a , b )

- **Endpoint variable ξ**, [DLMF 8.18.E2](https://dlmf.nist.gov/8.18.E2):
  The endpoint variable ξ.
  `DLMF.Statistical.Real.betaXi` ([definition](DLMF/IncompleteGamma/BetaAsymptotics.lean#L240)).

- **Taylor coefficients d_k at ξ**, [DLMF 8.18.E6](https://dlmf.nist.gov/8.18.E6):
  Taylor coefficients d_k at ξ.
  `DLMF.Statistical.Real.betaGeneratingCoeff` ([definition](DLMF/IncompleteGamma/BetaAsymptotics.lean#L249)).

- **Transition center x₀**, [DLMF 8.18.E8](https://dlmf.nist.gov/8.18.E8):
  The transition center x₀.
  `DLMF.Statistical.Real.betaCenter` ([definition](DLMF/IncompleteGamma/BetaAsymptotics.lean#L573)).

- **Signed transition variable, continuous with η/(x-x₀)>0**, [DLMF 8.18.E10](https://dlmf.nist.gov/8.18.E10):
  The signed transition variable, continuous with η/(x-x₀)>0.
  `DLMF.Statistical.Real.betaEta` ([definition](DLMF/IncompleteGamma/BetaAsymptotics.lean#L578)).

- **General-case transition variable ζ with its required branch**, [DLMF 8.18.E15](https://dlmf.nist.gov/8.18.E15):
  The general-case transition variable ζ with its required branch.
  `DLMF.Statistical.Real.betaZeta` ([definition](DLMF/IncompleteGamma/BetaAsymptotics.lean#L756)).

- **Inverse regularized incomplete beta on the real interval**, [DLMF 8.18.E18](https://dlmf.nist.gov/8.18.E18):
  Inverse of normalized incomplete Beta on [0,1].
  `DLMF.Statistical.Real.incBetaInverse` ([definition](DLMF/IncompleteGamma/BetaAsymptotics.lean#L975)).

### §8.19 Generalized Exponential Integral

<!-- retained entry 66 -->
- **Eₚ**, [8.19.1–4](https://dlmf.nist.gov/8.19.i):
  `DLMF.Confluent.genExpIntE` in
  [ExpIntegral](DLMF/Confluent/Basic/ExponentialIntegrals.lean#L25),
  `genExpIntEOnLog` and `genExpIntEExtended` in
  [ExponentialIntegral](DLMF/IncompleteGamma/ExponentialIntegral.lean#L28).
  `OnLog` retains the sheet; `Extended` assigns `1/(p-1)` at zero, whose
  DLMF meaning requires `Re p > 1`. The integrals in 8.19.2–4 have theorem
  representations, with no separately defined integral-based Eₚ object.

- **Generalized exponential-integral order derivatives and large-order polynomials**, [DLMF 8.19.v](https://dlmf.nist.gov/8.19.v):
  The higher-order generalized integrals are defined through repeated derivatives with respect top; these are order derivatives, distinct from derivatives with respect to the ordinary argument. L(p) in 8.19.27 is `DLMF.Confluent.genExpIntL` ([source](DLMF/IncompleteGamma/ExponentialIntegral.lean#L1122)); Aₖ(λ) in 8.20.4 is `DLMF.Confluent.expIntLargeOrderPolynomial` ([source](DLMF/IncompleteGamma/ExpIntegralAsymptotics.lean#L496)). The generalized trigonometric auxiliariesf,g in §8.21.18–19 are `DLMF.Confluent.genTrigAuxF`, `DLMF.Confluent.genTrigAuxG` ([source](DLMF/IncompleteGamma/SineCosine/SphericalSeries.lean#L425)).

  [DLMF 8.19.E27](https://dlmf.nist.gov/8.19.E27):
  The auxiliary integral L(p) for positive p.
  `DLMF.Confluent.genExpIntL` ([definition](DLMF/IncompleteGamma/ExponentialIntegral.lean#L1122)).

### §8.20 Asymptotic Expansions of E p ⁡ ( z )

- **Large-order polynomials A_k(λ), including A₀=1**, [DLMF 8.20.E4](https://dlmf.nist.gov/8.20.E4):
  Large-order polynomials A_k(λ), including A₀=1.
  `DLMF.Confluent.expIntLargeOrderPolynomial` ([definition](DLMF/IncompleteGamma/ExpIntegralAsymptotics.lean#L496)).

### §8.21 Generalized Sine and Cosine Integrals

<!-- retained entry 67 -->
- **Lower Si(a,z), Ci(a,z) and upper si(a,z), ci(a,z)**,
  [8.21.1–2](https://dlmf.nist.gov/8.21.E1) and
  [principal-value prose](https://dlmf.nist.gov/8.21.ii):
  `DLMF.Confluent.genSinIntOnLog`, `genCosIntOnLog`,
  `genSinIntTailOnLog`, `genCosIntTailOnLog`, `genSinInt`, `genCosInt`,
  `genSinIntTail`, `genCosIntTail` in
  [GammaRepresentations](DLMF/IncompleteGamma/SineCosine/GammaRepresentations.lean#L28).
  Lower functions use convergent series on logarithmic coordinates; upper
  functions use continued upper gamma. Principal functions specialize `w = log z`.
  Lower parameter poles remain exceptional; the upper functions are entire
  in the parameter. The ordinary Chapter 6 functions are different
  specializations and shifts, not naming aliases.

- **Generalized auxiliary f**, [DLMF 8.21.E18](https://dlmf.nist.gov/8.21.E18):
  Generalized auxiliary f.
  `DLMF.Confluent.genTrigAuxF` ([definition](DLMF/IncompleteGamma/SineCosine/SphericalSeries.lean#L425)).

- **Generalized auxiliary g**, [DLMF 8.21.E19](https://dlmf.nist.gov/8.21.E19):
  Generalized auxiliary g.
  `DLMF.Confluent.genTrigAuxG` ([definition](DLMF/IncompleteGamma/SineCosine/SphericalSeries.lean#L430)).

### §8.22 Mathematical Applications

- **Terminant, incomplete Riemann zeta and Debye integrals**, [DLMF 8.22](https://dlmf.nist.gov/8.22):
  F_p(z)=Γ(p)Γ(1−p,z)/(2π) occurs as an explicit expression in the Chapter 2 Stokes theorems ([source](DLMF/AsymptoticApproximations/Remainders/Stokes.lean#L110)); the distinct logarithmic-plane construction `DLMF.Airy.airyTerminator p w`, with z=exp w, equals e^z F_p(z) and is G_p(z) in 10.17.16 ([source](DLMF/Airy/Asymptotics/LaplaceSectors.lean#L118)). Neither should be confused with differently normalized terminants in the literature. ζₓ(s)=Γ(s)⁻¹∫₀ˣt^(s−1)/(eᵗ−1)dt,Re(s)>1, and the two unnormalized Debye integrals are explicitly defined in §8.22(ii); no matching local named constructions were found. Gamma/beta probability integrals and Erlang loss in §8.23 are application interpretations of existing functions, without a new local queueing function.

## Chapter 9 — Airy and related functions

Expanded review: all 20 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§9.1–9.20 checked; the matching heading is §9.8(i).

### §9.2 Differential Equation

<!-- retained entry extra68 -->
Fundamental definitions: [§9.2](https://dlmf.nist.gov/9.2)
is titled “Differential Equation”, not “Definitions”. Its Ai, Bi and derivatives
are `DLMF.Airy.airyAi`, `airyBi`, `airyAiDeriv`, `airyBiDeriv` in
[Basic](DLMF/Airy/Basic.lean#L42), constructed from regularized ₀F₁;
real restrictions `airyAiReal`, `airyBiReal`, `airyAiDerivReal`,
`airyBiDerivReal` are in [Framework](DLMF/Airy/Framework.lean#L25).
Integral formulas are bridge theorems, not alternative public Ai/Bi definitions.

- **Airy equation, power-series building blocks and Riccati substitution**, [DLMF 9.2](https://dlmf.nist.gov/9.2):
  `DLMF.Airy.IsAirySol` ([source](DLMF/Airy/Basic.lean#L68)) records the first-order pair forw″=zw. The actual entire building blocks `DLMF.Airy.airyF`, `DLMF.Airy.airyG`, `DLMF.Airy.airyFDeriv`, `DLMF.Airy.airyGDeriv` ([source](DLMF/Airy/Basic.lean#L27)) implement the series behind the Ai/Bi formulas; their defining series are described at §9.4, without a new Airy normalization. The Riccati solutionw′/w in 9.2.18 is a log-derivative expression. `DLMF.Airy.IsWellConditionedPairOn` ([source](DLMF/Airy/Framework.lean#L107)) packages the mathematical region condition for satisfactory pairs; it adds no numerical solver.

### §9.6 Relations to Other Functions

- **Airy variables, asymptotic coefficients, multipliers and terminant**, [DLMF 9.6.E1](https://dlmf.nist.gov/9.6.E1):
  ζ=(2/3)z^(3/2) has actual real `DLMF.Airy.airyZeta` and complex `DLMF.Airy.airyZetaComplex`, with logarithmic `DLMF.Airy.airyLogZeta` and inverse `DLMF.Airy.airyInverseZetaOnLog`. The uₖ,vₖ of §9.7, χ(x), the piecewise sector error multiplier and terminant are actual constructions in [Asymptotics/LaplaceSectors](DLMF/Airy/Asymptotics/LaplaceSectors.lean#L38) and the coefficient framework. The inherited log phase is required on sectors wider than the principal ζ-plane.

  [DLMF 9.6.E1](https://dlmf.nist.gov/9.6.E1):
  Principal Airy change of variable.
  `DLMF.Airy.airyZetaComplex` ([definition](DLMF/Airy/Framework.lean#L75)).

  [DLMF 9.6.E1](https://dlmf.nist.gov/9.6.E1):
  The variable `ζ = (2/3) x^{3/2}` (DLMF 9.6.1), for real `x`.
  `DLMF.Airy.airyZeta` ([definition](DLMF/Airy/Bessel.lean#L43)).

  [DLMF 9.6.E10](https://dlmf.nist.gov/9.6.E10):
  The inverse substitution on the logarithmic ζ plane.
  `DLMF.Airy.airyInverseZetaOnLog` ([definition](DLMF/Airy/Relations/BesselRepresentations.lean#L29)).

### §9.7 Asymptotic Expansions

- **Gamma-ratio error multiplier χ**, [DLMF 9.7.E3](https://dlmf.nist.gov/9.7.E3):
  The Gamma-ratio error multiplier χ.
  `DLMF.Airy.airyChi` ([definition](DLMF/Airy/Asymptotics/LaplaceSectors.lean#L38)).

- **Piecewise complex error multiplier in 9.7.17; the phase of ζ is inherited from z**, [DLMF 9.7.E17](https://dlmf.nist.gov/9.7.E17):
  The piecewise complex error multiplier in 9.7.17; the phase of ζ is inherited from z.
  On the ray `|arg z| = 2π/3` we have `sin(ph ζ) = 0`, and DLMF's `min(|csc(ph ζ)|, χ + 1)` is
  `χ + 1`; the case is written out because Lean's `0⁻¹ = 0` would give `0` (corrected 2026-10-21).
  The last case is used only for `2π/3 < |arg z| < π`: the 9.7.17 statements assume
  `z ∈ slitPlane`, which excludes `|arg z| = π`, where `cos(ph ζ) = 0` and DLMF gives no bound.
  `DLMF.Airy.airyErrorMultiplier` ([definition](DLMF/Airy/Asymptotics/LaplaceSectors.lean#L106)).

- **Terminant, with an explicit logarithmic argument to retain the Gamma branch**, [DLMF 9.7.E22](https://dlmf.nist.gov/9.7.E22):
  The terminant, with an explicit logarithmic argument to retain the Gamma branch.
  `DLMF.Airy.airyTerminator` ([definition](DLMF/Airy/Asymptotics/LaplaceSectors.lean#L118)).

### §9.8 Modulus and Phase

- **Airy modulus/phase coefficient families and selected zeros**, [DLMF 9.8](https://dlmf.nist.gov/9.8):
  Additional coefficient constructions for M,N,θ,φ are `DLMF.Airy.airyModulusCoeff`, `DLMF.Airy.airyDerivModulusCoeff`, `DLMF.Airy.airyReciprocalCoeff`, `DLMF.Airy.airyPhaseCoeff`, `DLMF.Airy.airyDerivPhaseCoeff`, and their finite sums ([source](DLMF/Airy/ModulusPhase/Representations.lean#L39)). In §9.9, all real zero families `DLMF.Airy.airyAiZero`, `DLMF.Airy.airyAiDerivZero`, `DLMF.Airy.airyBiZero`, `DLMF.Airy.airyBiDerivZero`, the two complex Bi families, their upper-sector set and continuous-index extensions are actual constructions ([source](DLMF/Airy/Zeros/RealAndAi.lean#L33)). The asymptoticT,U,V,W in 9.9.6–21 are represented through the corresponding zero/value expansions rather than four independently chosen global functions; exact zero families are retained, decimal tables excluded.

<!-- retained entry 68 -->
- **Airy moduli M, N and continuous phases θ, φ**, [9.8.1–8 and branch prose](https://dlmf.nist.gov/9.8.i):
  `DLMF.Airy.airyModulus`, `airyDerivModulus`, `airyPhase`, and
  `airyDerivPhase` in
  [Representations](DLMF/Airy/ModulusPhase/Representations.lean#L29).
  The phases are defined by integrals, with values `π/6` and `-π/6` at zero,
  so they retain the continuous branches rather than principal arctangents.
  DLMF restricts this section to real `x ≤ 0`.

### §9.12 Scorer Functions

- **Scorer functions and inhomogeneous equation**, [DLMF 9.12](https://dlmf.nist.gov/9.12):
  Hi is constructed by its entire series `DLMF.Airy.scorerHi`, Gi by `scorerGi=airyBi−scorerHi`; their derivative constructions, `DLMF.Airy.scorerHiCoeff`, `DLMF.Airy.scorerGiCoeff`, `DLMF.Airy.IsScorerSol`, and `DLMF.Airy.IsAiryInhomSol` also exist ([source](DLMF/Airy/Scorer/Representations.lean#L30)). Integral representations and independent series constructions are separate objects. The third-order Wronskian and `DLMF.Airy.IsWellConditionedTripleOn` package the stated satisfactory-triple properties.

  [DLMF 9.12.E17](https://dlmf.nist.gov/9.12.E17):
  The entire Scorer function Hi, specified by its Maclaurin series.
  `DLMF.Airy.scorerHi` ([definition](DLMF/Airy/Scorer/Representations.lean#L33)).

### §9.13 Generalized Airy Functions

- **Generalized Airy families in three normalizations**, [DLMF 9.13.i](https://dlmf.nist.gov/9.13.i):
  In addition to `DLMF.Airy.generalizedAiryOrder`, `DLMF.Airy.generalizedAiryZeta`, there are `DLMF.Airy.generalizedAiryF`, `DLMF.Airy.generalizedAiryG`, `DLMF.Airy.generalizedAiryA`, `DLMF.Airy.generalizedAiryB` and their four derivative constructions, `DLMF.Airy.IsGenAirySol`, `DLMF.Airy.olverAiryVariable`, `DLMF.Airy.olverAiryU`, `DLMF.Airy.olverAiryVBar`, `DLMF.Airy.olverAiryW`, `DLMF.Airy.smirnovAiryU1`, `DLMF.Airy.smirnovAiryU2`, and `DLMF.Airy.smirnovAiryVariable` ([source](DLMF/Airy/Generalized.lean#L22)). The entire hypergeometric Aₙ,Bₙ constructions and their positive-real Bessel identities give the continuation without making principal Bessel formulas globally equivalent. Olver's overbar is a separate solution name, not complex conjugation; odd/even m and the scaled independent variable matter.

  [DLMF 9.13.E3](https://dlmf.nist.gov/9.13.E3):
  The fractional Bessel order p=1/(n+2).
  `DLMF.Airy.generalizedAiryOrder` ([definition](DLMF/Airy/Generalized.lean#L22)).

  [DLMF 9.13.E3](https://dlmf.nist.gov/9.13.E3):
  The generalized Airy argument.
  `DLMF.Airy.generalizedAiryZeta` ([definition](DLMF/Airy/Generalized.lean#L25)).

  [DLMF 9.13.E14](https://dlmf.nist.gov/9.13.E14):
  The scaled independent variable t in Olver's normalization.
  `DLMF.Airy.olverAiryVariable` ([definition](DLMF/Airy/Generalized.lean#L42)).

  [DLMF 9.13.E20](https://dlmf.nist.gov/9.13.E20):
  Smirnov's normalized first solution on the positive real axis.
  `DLMF.Airy.smirnovAiryU1` ([definition](DLMF/Airy/Generalized.lean#L53)).

  [DLMF 9.13.E21](https://dlmf.nist.gov/9.13.E21):
  Smirnov's normalized second solution on the positive real axis.
  `DLMF.Airy.smirnovAiryU2` ([definition](DLMF/Airy/Generalized.lean#L59)).

  [DLMF 9.13.E22](https://dlmf.nist.gov/9.13.E22):
  Smirnov/Olver variable conversion, DLMF 9.13.22.
  `DLMF.Airy.smirnovAiryVariable` ([definition](DLMF/Airy/Generalized.lean#L1314)).

- **Reid contour Airy families and finite-part representatives**, [DLMF 9.13.ii](https://dlmf.nist.gov/9.13.ii):
  `DLMF.Airy.reidAiryA`, `DLMF.Airy.reidAiryB0`, and `DLMF.Airy.reidAiryB` are distinct actual constructions ([source](DLMF/Airy/GeneralizedContours.lean#L32)), supported by `DLMF.Airy.reidKernel`, `DLMF.Airy.reidRay`, `DLMF.Airy.reidArc`, `DLMF.Airy.reidContour`, `DLMF.Airy.reidTaylorCoeff`, `DLMF.Airy.reidTaylorTail`, and `DLMF.Airy.reidFinitePartH`. The A-family accepts complex p with the specified log branch, whereas the B-families take integral p and include finite-part continuation when the ray endpoint is singular. Contour direction and normalization factors distinguish these solutions even when their differential equations agree.

  [DLMF 9.13.E25](https://dlmf.nist.gov/9.13.E25):
  Reid's A1,A2,A3 on L1,L2,L3 of Figure 9.13.1.
  `DLMF.Airy.reidAiryA` ([definition](DLMF/Airy/GeneralizedContours.lean#L32)).

  [DLMF 9.13.E26](https://dlmf.nist.gov/9.13.E26):
  The normalized contour integral B₀(z,p) over the positively oriented closed contour L₀, for integral p; this is a function value, not a path object.
  `DLMF.Airy.reidAiryB0` ([definition](DLMF/Airy/GeneralizedContours.lean#L39)).

### §9.14 Incomplete Airy Functions

- **Incomplete Airy integrals at either endpoint**, [DLMF 9.14](https://dlmf.nist.gov/9.14):
  The contour integral with one variable real or complex endpoint gives two actual constructions `DLMF.Airy.incompleteAiryAi` and `DLMF.Airy.incompleteAiryAiLower` ([source](DLMF/Airy/Incomplete.lean#L23)). Their contour normalization and endpoint direction differ; their sum and complete-endpoint limits are bridge theorems to the existing Ai. Neither is a numerical truncation algorithm.

## Chapter 10 — Bessel functions

Expanded review: all 77 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§10.1–10.77 checked; matching headings are §10.2,
§10.18(i), §10.25, §10.47, §10.61 (including (i)), and §10.68(i).

### §10.1 Special Notation

- **Euler differential operator**, [DLMF 10.1](https://dlmf.nist.gov/10.1):
  ϑ=z d/dz is `DLMF.Hypergeometric.eulerTheta`
  ([source](DLMF/Hypergeometric/Generalized.lean#L39)). The ψ notation reuses
  digamma; historical alternative names for J, Y, I and K do not define additional
  normalizations.

### §10.2 Definitions

<!-- retained entry 69 -->
- **Bessel equation**, [10.2.1](https://dlmf.nist.gov/10.2.E1): expressible
  through `DLMF.Struve.besselResidual` with the homogeneous sign convention in
  [Struve/Basic](DLMF/Struve/Basic/Functions.lean#L23), or directly as a derivative identity.
  `DLMF.Bessel.IsRealBesselSolution` in
  [SturmZeros](DLMF/Bessel/SturmZeros.lean#L355) is a real differential-system predicate.

<!-- retained entry 73 -->
- **General cylinder function Cν**, [§10.2(ii) prose](https://dlmf.nist.gov/10.2.ii):
  finite constant linear combinations of the preceding functions; no separate
  local definition or structure for this notation.

The functions above use a single principal-power convention, with separate
logarithmic constructions `airyBesselJOnLog`, `airyBesselYOnLog`,
`airyHankel1OnLog`, and `airyHankel2OnLog` in
[Airy/Framework](DLMF/Airy/Framework.lean#L87) when sheets are needed.
These logarithmic formulas must be used with their parameter hypotheses.

<!-- retained entry 70 -->
- **Jν**, [10.2.2](https://dlmf.nist.gov/10.2.E2): Mathlib
  `Complex.besselJ` in
  [Bessel](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Bessel.lean#L55),
  a principal-power times regularized ₀F₁ definition. Local
  `besselJ_eq_regularized` in [Basic](DLMF/Bessel/RegularizedSeries.lean#L37)
  is a bridge, not another definition.

- **Entire regularized core and explicit logarithmic constructions**,
  [DLMF 10.2.E2](https://dlmf.nist.gov/10.2.E2),
  [continuation §10.11](https://dlmf.nist.gov/10.11):
  `DLMF.Bessel.besselJCore μ s` is the entire factor
  ₀F̃₁(;μ+1;−s/4), so Jμ(z)=(z/2)^μ besselJCore μ (z²)
  ([source](DLMF/Bessel/Lommel.lean#L75)); it is not the whole J function.
  Alongside the retained Airy logarithmic constructions, the actual
  `DLMF.Mathieu.besselJExp`, `besselYExp`, and `mathieuCylExp`
  ([source](DLMF/Mathieu/Modified/Basic/Functions.lean#L72)) retain the unwrapped argument
  in Jμ(h exp z), Yμ(h exp z) and J/Y/H¹/H². `mathieuCyl` in the same file
  and `DLMF.Spheroidal.spheroidalCylinder`
  ([source](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L388)) select the four principal cylinder
  functions. These selectors do not represent every constant linear combination
  denoted by DLMF's general Cν. Continued ze^(mπi) means a continued argument,
  not merely evaluation at an equal complex point on the principal sheet.

<!-- retained entry 71 -->
- **Yν, including integral orders**, [10.2.3–4](https://dlmf.nist.gov/10.2.E3):
  `DLMF.Bessel.besselY` in [Basic](DLMF/Bessel/Basic.lean#L28), with order limits
  at integers. The separately defined `besselYLaplace` is an auxiliary
  integral in Y representations in
  [YIntegralRep](DLMF/Bessel/YIntegralRep.lean#L252), not another definition of
  the whole Y function.

<!-- retained entry 72 -->
- **Hankel H¹ and H²**, [defining asymptotics 10.2.5–6](https://dlmf.nist.gov/10.2.E5):
  `DLMF.Bessel.hankelH1`, `hankelH2` in
  [SecondKind](DLMF/Bessel/SecondKind.lean#L514), defined as `J ± iY`.

### §10.6 Recurrence Relations and Derivatives

- **Scaled cylinder family and reciprocal derivative**,
  [DLMF 10.6.E4–6](https://dlmf.nist.gov/10.6.E4):
  fν(z)=z^p Cν(λz^q) is an expression in the underlying cylinder functions;
  no separately named complete p,q,λ family was found.
  The operator f↦z⁻¹f′ used in 10.6.6,10.29.4,10.49.14–16 and10.51.3/6
  is `DLMF.Bessel.zRecipDeriv`
  ([source](DLMF/Bessel/Elementary.lean#L544)); powers of the operator mean
  iteration, with the domain excluding z=0 unless a removable value is supplied.

- **Same-order, two-argument cross-products pν,qν,rν,sν**,
  [DLMF 10.6.E8](https://dlmf.nist.gov/10.6.E8):
  these are the four determinants formed from Jν(a),Yν(a),Jν(b),Yν(b),
  with neither, either or both argument columns differentiated. No named Lean
  equivalents were found. `DLMF.Bessel.besselW`
  ([source](DLMF/Bessel/Zeros.lean#L58)) instead combines different orders at
  one argument, so it is not pν or one of its argument derivatives.

### §10.9 Integral Representations

- **Independent auxiliary integrals in J/Y representations**,
  [DLMF 10.9.E5–6](https://dlmf.nist.gov/10.9.E5):
  the retained `DLMF.Bessel.besselYLaplace` is
  2(z/2)^ν/(√πΓ(ν+½)) times ∫₀∞e^(−zt)(1+t²)^(ν−½)dt, with actual
  integrand `yLaplaceKernel`
  ([source](DLMF/Bessel/YIntegralRep.lean#L40)). It is the second component of
  the Y representation, not the complete function Y. Schläfli's J representation
  is `besselJ_eq_schlafli`
  ([source](DLMF/Bessel/Schlafli.lean#L586)); actual auxiliary constructions
  `schlafliCircle` and `schlafliRay` in that file are the circle and ray pieces
  of a Hankel loop in exponential coordinates. `schlafliBoundary` is the
  integration-by-parts continuation of the radial integral to its closed
  half-plane boundary ([source](DLMF/Bessel/Schlafli.lean#L710)). These integral
  objects and the series-defined J are separate constructions linked by theorems.

### §10.10 Continued Fractions

- **Bessel quotient continued fractions**, [DLMF 10.10.E1–2](https://dlmf.nist.gov/10.10.E1),
  [modified quotients 10.33.E1–2](https://dlmf.nist.gov/10.33.E1):
  the coefficients are the explicit ν,z-dependent expressions in these
  equations. No separately named Bessel-specific fraction object was found.
  `DLMF.cfContinuants`, `cfTail` and `HasContinuedFraction`
  ([source](DLMF/Core/Framework.lean#L148)) provide the generic finite
  continuants, their ratios, and convergence predicate. They preserve finite
  termination and avoid evaluating nested intermediate zero denominators.

### §10.17 Asymptotic Expansions for Large Argument

- **Hankel coefficients aₖ and derivative coefficients bₖ, phase ω**,
  [DLMF 10.17.E1–2](https://dlmf.nist.gov/10.17.E1),
  [10.17.E8](https://dlmf.nist.gov/10.17.E8):
  a₀=1 and aₖ=(½−ν)ₖ(½+ν)ₖ/[(-2)^k k!]; b₀=1 and the explicitly
  specified bₖ give the differentiated expansions. The phase is
  ω=z−νπ/2−π/4. There are no independently named local aₖ/bₖ/ω objects.
  The all-order aₖ do have an existing equivalent coefficient expression:
  `DLMF.Confluent.tricomiCoeff (ν+1/2) (2*ν+1) k / 2^k`
  ([source](DLMF/Confluent/Asymptotics/LargeArgument.lean#L34)). The Bessel
  asymptotic theorems use this Tricomi coefficient with their scale (2z)^(-k−½)
  ([source](DLMF/Bessel/Asymptotics.lean#L68)); the unscaled Tricomi coefficient is not aₖ. Exact coefficient families remain in scope.

- **Normalized remainders, variation factor and scaled terminant**,
  [DLMF 10.17.E13–17](https://dlmf.nist.gov/10.17.E13):
  Rℓ⁺ and Rℓ⁻ are the exact normalized Hankel truncation errors, and
  Rₘ,ℓ⁺/⁻ are their second-level remainders after removing the displayed
  terminant sum. No separately named Bessel remainder constructions were found.
  χ(ℓ)=√πΓ(ℓ/2+1)/Γ(ℓ/2+½) is the existing `DLMF.Airy.airyChi`
  ([source](DLMF/Airy/Asymptotics/LaplaceSectors.lean#L38)); variation reuses
  Chapter 2's variational operator. The terminant
  G_p(z)=e^zΓ(p)Γ(1−p,z)/(2π) is the actual
  `DLMF.Airy.airyTerminator p w` with z=exp w
  ([source](DLMF/Airy/Asymptotics/LaplaceSectors.lean#L118)). Its explicit log
  coordinate preserves the incomplete-Gamma sheet. This is G_p, and differs by
  the factor e^z from F_p in 8.22.1.

### §10.18 Modulus and Phase Functions

<!-- retained entry 74 -->
- **Bessel Mν, Nν, θν and φν**, [10.18.1–3](https://dlmf.nist.gov/10.18.i):
  no corresponding named Lean objects found. Norms of H¹ and its derivative
  give the moduli, but `Complex.arg` alone would not give the prescribed
  continuous phases with the limits at zero.

### §10.19 Asymptotic Expansions for Large Order

- **Large-order comparison, oscillatory phase and transition polynomials**,
  [DLMF 10.19.E1](https://dlmf.nist.gov/10.19.E1),
  [10.19.E5](https://dlmf.nist.gov/10.19.E5),
  [10.19.E8–15](https://dlmf.nist.gov/10.19.E8):
  the fixed-z comparison (ez/(2ν))^ν/√(2πν) is
  `DLMF.Bessel.besselLargeOrderMain`, with separately defined exact correction
  `besselLargeOrderCorr`
  ([source](DLMF/Bessel/LargeOrder.lean#L295)). The phase
  ξ=ν(tanβ−β)−π/4 is an expression, without a named local object.
  Pₖ(a),Qₖ(a),Rₖ(a),Sₖ(a) are the four exact polynomial families of the
  Airy transition expansions, with displayed rational coefficients in 10.19.10,
  11,14,15; no named local equivalents were found. Uₖ,Vₖ are the Debye
  polynomials of 10.41, recorded there. These asymptotic definitions are distinct
  from numerical coefficient tables.

### §10.20 Uniform Asymptotic Expansions for Large Order

- **Turning-point coordinate and four coefficient families**,
  [DLMF 10.20.E1–3](https://dlmf.nist.gov/10.20.E1),
  [10.20.E10–13](https://dlmf.nist.gov/10.20.E10):
  ζ(z) is the signed turning-point coordinate determined by its differential
  equation and the real quadratures on either side of z=1; its smooth removable
  behavior at1 and its continued complex branch are part of the definition.
  Aₖ(ζ),Bₖ(ζ),Cₖ(ζ),Dₖ(ζ) are the exact coefficient functions built from
  Debye and Airy coefficients, including their removable ζ=0 values. No
  Bessel-specific local ζ or A/B/C/D constructions were found. Generic
  `DLMF.asymptoticCoeff` is not a substitute for their defining normalization.

- **Continuation boundary and exact constants**,
  [DLMF 10.20.E15–18 and prose](https://dlmf.nist.gov/10.20.E15):
  the continued inverse-map boundary curves define the closed eye-shaped
  region K. The positive τ₀ is selected by τ₀=cothτ₀ and
  c=√(τ₀²−1). These exact curves, region and constants have no named local
  constructions. Their decimal displays and the figures are excluded, while
  their exact definitions remain in scope.

### §10.21 Zeros

- **Indexed ordinary and derivative zeros and continuous indices**,
  [DLMF 10.21.i](https://dlmf.nist.gov/10.21.i),
  [10.21.ii](https://dlmf.nist.gov/10.21.ii),
  [10.21.iv](https://dlmf.nist.gov/10.21.iv):
  jν,m,j′ν,m,yν,m,y′ν,m enumerate the positive real zeros of J,Y and their
  argument derivatives, except j′₀,₁=0. The continuous extensions ρν(t),σν(t)
  use zeros of Jν(x)cosπt+Yν(x)sinπt and the specified initial conventions
  ρν(0)=0,σν(0)=j′ν,1. Their first/second forward differences are also
  introduced, and j″ν,m denotes the indexed second-derivative zeros in 10.21.15.
  No dedicated indexed or continuous-index Bessel-zero constructions were found.
  `DLMF.orderedZero` ([source](DLMF/Core/Framework.lean#L180)) is a generic
  epsilon-selected zero with a separate existence/specification obligation.
  Existing first-zero results instead use sInf of a real positive-zero set
  ([source](DLMF/Bessel/Zeros.lean#L98)); neither is an alias for all four
  indexed families or their exceptional zero convention.

- **Zero-expansion coefficients and inverse turning-point coordinates**,
  [DLMF 10.21.E19–31](https://dlmf.nist.gov/10.21.E19),
  [10.21.E40–45](https://dlmf.nist.gov/10.21.E40):
  the McMahon a,b,c shifts, the Airy-related α,α′, and the coefficient families
  αₖ,βₖ,α′ₖ,β′ₖ are defined by the stated exact formulas. The inverse z(ζ)
  of 10.20 and h(ζ)=(4ζ/(1−z²))^(1/4) enter the uniform zero expansions.
  No named local equivalents were found for these Bessel-zero coefficient
  families. Branches and the removable turning-point values cannot be obtained
  merely by taking unrelated principal roots.

- **Complex-zero shifts, cross-product scales and Riccati–Bessel functions**,
  [DLMF 10.21.E46–54](https://dlmf.nist.gov/10.21.E46),
  [10.21.xi](https://dlmf.nist.gov/10.21.xi):
  a=(log3)/2 and d=(log2)/2 are exact constants in the complex-zero formulas;
  the later α,p,q,r are the displayed a,b,ν-dependent cross-product zero scales.
  They are expressions without separate local definitions. Riccati–Bessel
  functions are √(πx/2)Jν(x) and √(πx/2)Yν(x); for ν=n+½, these are x times the
  integer-index spherical j_n,y_n; no named local family was found. Decimal
  zero values and decimal displays of the exact shifts are excluded: numerical.

- **Rayleigh function**, [DLMF 10.21.E55](https://dlmf.nist.gov/10.21.E55):
  σ_n(ν)=Σ_{m≥1} jν,m^(−2n), with the stated ν>-1 and positive integral n,
  is a separate zero-sum family. No named local equivalent was found; first-zero
  bounds alone do not construct it.

### §10.22 Integrals

- **Geometric integration variables**, [DLMF 10.22.E71–73](https://dlmf.nist.gov/10.22.E71):
  cosφ,coshχ are fixed by the stated a,b,c relations; the triangle factor is
  A=s(s−a)(s−b)(s−c),s=(a+b+c)/2. They are expressions rather than named
  local special functions. The fractional/repeated Bessel integrals in 10.22.36
  use the ordinary integral operators; the section's other evaluations introduce
  no further named Bessel function family.

- **Hankel/Bessel transform and Weber-type inversion pairs**,
  [DLMF 10.22.E76–79](https://dlmf.nist.gov/10.22.E76):
  the Hankel transform is g(y)=∫₀∞f(x)Jν(xy)√(xy)dx, with the symmetric
  √(xy) normalization and the stated inversion conditions. Weber's transform
  uses the cross-product kernel Jν(xt)Yν(at)−Yν(xt)Jν(at) on x≥a, its
  denominator Jν(at)²+Yν(at)², and the associated inversion. The second
  inversion pair10.22.79 uses √(xt)(cJν(xt)+t^(2ν)J₋ν(xt)) and the
  denominator c²+2c cos(νπ)t^(2ν)+t^(4ν), with c>0,0<ν<1.
  No named transform definitions were found in Mathlib, TauCeti or this project.
  `DLMF.AlgebraicAnalytic.tendsto_hankel_kernel`
  ([source](DLMF/AlgebraicAnalytic/Spectral/Theory.lean#L478)) states the
  corresponding symmetric-kernel completeness limit, but it is a theorem
  statement, not a transform definition. Specialized exact Bessel-transform
  integrals also occur in
  [Confluent/Integrals/BesselTransforms](DLMF/Confluent/Integrals/BesselTransforms.lean#L47).

### §10.23 Sums

- **Graf–Gegenbauer addition coordinates**,
  [DLMF 10.23.E6](https://dlmf.nist.gov/10.23.E6):
  w²=u²+v²−2uv cosα, w cosχ=u−v cosα, w sinχ=v sinα, with branches
  w→u,χ→0 as v→0, define the auxiliary coordinates reused in 10.60.
  No named local construction with these continuation conditions was found.

- **Neumann polynomials and Neumann/Fourier–Bessel coefficients**,
  [DLMF 10.23.E11–13](https://dlmf.nist.gov/10.23.E11),
  [10.23.E19](https://dlmf.nist.gov/10.23.E19):
  O_n(t) is defined by the stated rational generating function and finite
  inverse-power formula, with O₀=1/t. The Neumann expansion coefficient aₖ is
  the specified Cauchy-contour functional involving Oₖ; Fourier–Bessel a_m is
  the weighted integral on [0,1], normalized by Jν+1(jν,m)². No matching
  named local constructions were found. The existing
  `DLMF.Bessel.neumannCoeff`, `neumannLinCoeff`
  ([source](DLMF/Bessel/NeumannSeries.lean#L186)) extract coefficients of
  general locally constructed double series; they are not O_n or those
  contour/Fourier coefficient functionals. `powerNeumannCoeff`
  ([source](DLMF/Bessel/NeumannSeries.lean#L339)) does represent the separate
  exact (λ+2k)Γ(λ+k)/k! coefficient in 10.23.15 and10.44.4.

### §10.24 Functions of Imaginary Order

- **Real normalized imaginary-order pair and continuous Gamma phase**,
  [DLMF 10.24.E2–3](https://dlmf.nist.gov/10.24.E2):
  J̃ν(x)=sech(πν/2)Re J_(iν)(x),
  Ỹν(x)=sech(πν/2)Re Y_(iν)(x), for real ν and x>0, have no named local
  equivalents. The phase γν is fixed by Γ(1+iν)=(πν/sinhπν)^(1/2)e^(iγν)
  with continuity and γ₀=0. No matching continuous phase construction was found.
  `DLMF.Confluent.coulombSigma 0 ν`
  ([source](DLMF/Coulomb/Basic/Functions.lean#L67)) takes the principal `Complex.arg`
  and therefore cannot supply this unwrapped phase globally.

### §10.25 Definitions

<!-- retained entry 75 -->
- **Modified Bessel equation**, [10.25.1](https://dlmf.nist.gov/10.25.E1):
  expressible through the sign choice of `DLMF.Struve.besselResidual`; no
  separate local homogeneous-equation predicate is needed by the library.

<!-- retained entry 77 -->
- **General modified cylinder function Zν**, [§10.25(ii) prose](https://dlmf.nist.gov/10.25.ii):
  represented by constant linear combinations of I and `exp(νπi) K`;
  no separate named object.

<!-- retained entry 76 -->
- **Iν and Kν**, [10.25.2–3](https://dlmf.nist.gov/10.25.E2):
  `DLMF.Bessel.besselI`, `besselK` in [Modified](DLMF/Bessel/Basic.lean#L38).
  I uses the regularized ₀F₁ series; K uses the I-connection formula with
  order limits at integers. `airyBesselIOnLog`, `airyBesselKOnLog` in
  [Airy/Framework](DLMF/Airy/Framework.lean#L84) retain logarithmic arguments.
  `besselKMoment 0` in [KIntegralRep](DLMF/Bessel/KIntegralRep.lean#L126)
  is the independently defined whole-line integral moment used in integral
  representations; normalization to K is a theorem, not an alias.

- **Independent real I definition**, [DLMF 10.25.E2](https://dlmf.nist.gov/10.25.E2):
  in addition to the retained complex `DLMF.Bessel.besselI`, pinned TauCeti has
  `Real.besselI` ([source](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/BesselI.lean#L69)),
  defined as the real part of the corresponding complex regularized series.
  Its `Real.hasSum_besselI` records the classical real power series on x>0.
  For nonintegral order at negative x it is a real part, not the complex
  principal I value; its totalized zero values also require their stated domain
  interpretation. This real construction does not replace the all-complex local
  I or K definitions.

### §10.32 Integral Representations

- **Independent modified-Bessel integral and its moments**,
  [DLMF 10.32.E9](https://dlmf.nist.gov/10.32.E9):
  `DLMF.Bessel.besselKKernel ν z t=exp(−z cosh t+νt)` and
  `besselKMoment j ν z=∫ℝ cosh(t)^j besselKKernel ν z t dt`
  ([source](DLMF/Bessel/KIntegralRep.lean#L45)) are actual independently
  constructed integral objects. Kν(z)=½ besselKMoment 0 ν z on Re z>0 is
  `besselK_eq_half_integral`; `besselK_eq_integral_cosh` gives the equivalent
  half-line cosh(νt) representation
  ([source](DLMF/Bessel/KIntegralRep.lean#L654)). The whole-line version has the factor ½. The Mellin–Barnes formulas10.32.13–14
  are integral representations, without another named K construction.

### §10.40 Asymptotic Expansions for Large Argument

- **Order-derivative coefficients and modified remainders**,
  [DLMF 10.40.E8–10](https://dlmf.nist.gov/10.40.E8),
  [10.40.E13](https://dlmf.nist.gov/10.40.E13):
  α₀(ν)=1 and αₖ(ν) are the exact product-times-reciprocal-sum coefficients
  of the order derivative of K. At apparent individual reciprocal poles the
  canceled polynomial/continuous interpretation is necessary. No named local α
  family was found. Rℓ(ν,z) and Rₘ,ℓ(ν,z) are the normalized finite K
  truncation error and its terminant re-expansion error, without separate named
  Bessel constructions. The aₖ,bₖ,χ and G_p reuse10.17, rather than defining
  new normalizations.

### §10.41 Asymptotic Expansions for Large Order

- **Debye coordinate and polynomial families**,
  [DLMF 10.41.E7–11](https://dlmf.nist.gov/10.41.E7):
  η=√(1+z²)+log(z/(1+√(1+z²))) and p=(1+z²)^(-1/2) use the specified
  real/principal values and continuation from positive z. No independently named
  local Bessel η,p construction was found. The exact Debye Uₖ polynomial is
  already `DLMF.Struve.angerDebyePoly k`
  ([source](DLMF/Struve/Coefficients.lean#L26)): its initial value1 and derivative
  plus zero-normalized polynomial antiderivative recurrence agree with 10.41.9.
  The name reflects its use in Chapter 11, not a different recurrence. V₀=1
  and Vₖ₊₁=Uₖ₊₁−½p(1−p²)Uₖ−p²(1−p²)U′ₖ are given exactly there;
  no separate named Vₖ family was found. Exact rational coefficients remain
  in scope; numerical coefficient tables are excluded.

### §10.43 Integrals

- **Bickley function, integral definitions and continuation**,
  [DLMF 10.43.E11–12](https://dlmf.nist.gov/10.43.E11):
  Ki_α(x)=Γ(α)^(-1)∫ₓ∞(t−x)^(α−1)K₀(t)dt for Reα>0,x>0,
  continued analytically elsewhere, and equivalently
  ∫₀∞exp(−x cosh t)/(cosh t)^α dt for x>0. No named construction of either
  integral or the continued Bickley family was found. Ki₀=K₀ and negative
  integral orders are derivatives of K₀; these identifications do not by
  themselves construct the full α-family.

- **Kontorovich–Lebedev transform**, [DLMF 10.43.E30–31](https://dlmf.nist.gov/10.43.E30):
  f(y)=(2y/π²)sinh(πy)∫₀∞g(x)K_(iy)(x)dx/x, with inverse
  g(x)=∫₀∞f(y)K_(iy)(x)dy under either specified set of conditions.
  No named local or upstream transform construction was found. The dx/x weight,
  prefactor and imaginary order are part of this normalization.

### §10.45 Functions of Imaginary Order

- **Modified real imaginary-order pair**, [DLMF 10.45.E2](https://dlmf.nist.gov/10.45.E2):
  Ĩν(x)=Re I_(iν)(x), K̃ν(x)=K_(iν)(x), for real ν,x>0, have no named
  local equivalents. Unlike10.24's J̃/Ỹ, no sech factor occurs. Their
  small-x formulas reuse the continuous γν of 10.24, with its phase qualification.

### §10.46 Generalized and Incomplete Bessel Functions; Mittag-Leffler Function

- **Wright generalized Bessel function and Mittag-Leffler family**,
  [DLMF 10.46.E1](https://dlmf.nist.gov/10.46.E1),
  [10.46.E3](https://dlmf.nist.gov/10.46.E3):
  φ(ρ,β;z)=Σₖ≥0 z^k/[k!Γ(ρk+β)] for realρ>−1, and
  E_(a,b)(z)=Σₖ≥0 z^k/Γ(ak+b) for a>0, are exact entire series. No named
  constructions were found in Mathlib, TauCeti or this project. Wright omega
  and Mittag-Leffler partial-fraction expansions elsewhere in the project are
  different objects. Incomplete Bessel/Hankel functions are only referenced
  here, without a new explicit defining formula in this section.

### §10.47 Definitions and Basic Properties

- **Spherical equations and cylinder-quotient domains**,
  [DLMF 10.47.E1–9](https://dlmf.nist.gov/10.47.E1):
  the two spherical equations have coefficient2z on w′ and ordinary/modified
  signs; no separately named local spherical-equation predicates were found.
  In the retained `DLMF.Spheroidal.spheroidalPsi` mapping, case1 explicitly
  uses entire `DLMF.sphericalJ`; cases2,3,4 use the principal square root
  of π/(2z) times the principal Y/H cylinder
  ([source](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L400)). They represent the DLMF spherical y/h functions on the intended slit-plane domain. Values at 0 and
  continued negative-axis values must not be inferred from the totalized
  principal quotient. The DLMF convention throughout10.47–60 is n∈ℕ.

<!-- retained entry 78 -->
- **Spherical jₙ and modified i¹ₙ**, [10.47.3](https://dlmf.nist.gov/10.47.E3),
  [10.47.7](https://dlmf.nist.gov/10.47.E7):
  `DLMF.sphericalJ`, `DLMF.sphericalI` in
  [Framework](DLMF/Core/Framework.lean#L172), defined by regularized series
  that include their removable values at zero. These avoid interpreting a
  totalized square-root quotient as the value at zero.

<!-- retained entry 79 -->
- **Spherical yₙ, h¹ₙ, h²ₙ**,
  [10.47.4–6](https://dlmf.nist.gov/10.47.E4),
  are cases 2, 3 and 4 of `DLMF.Spheroidal.spheroidalPsi` in
  [Spheroidal/Basic](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L400). These actual
  square-root-times-cylinder definitions carry the principal branch and
  exclude zero in their intended domains. There are no extra public
  spherical-Y/H aliases.

<!-- retained entry 80 -->
- **Modified spherical i²ₙ and kₙ**,
  [10.47.8–9](https://dlmf.nist.gov/10.47.E8): no separate corresponding
  definitions found. They can be expressed using half-integer I and K,
  but those expressions do not supply named spherical objects or endpoint
  conventions.

### §10.49 Explicit Formulas

- **Bessel polynomial and finite square-sum coefficients**,
  [DLMF 10.49.ii prose](https://dlmf.nist.gov/10.49.ii),
  [10.49.E17](https://dlmf.nist.gov/10.49.E17):
  Σₖ₌₀ⁿ aₖ(n+½)z^(n−k), called the Bessel polynomial here, is the actual
  `DLMF.OrthogonalPolynomials.reverseBesselPolynomial n z`
  ([source](DLMF/OrthogonalPolynomials/Associated.lean#L77)). The separate
  `besselPolynomial 2 n z` in the same file is the unreversed classical y_n(z);
  its general a parameter belongs to 18.34. The exact
  sₖ(n+½)=(2k)!(n+k)!/[2^(2k)(k!)²(n−k)!],0≤k≤n, define the finite
  sums/differences of squares; no named local sₖ construction was found.

### §10.58 Zeros

- **Indexed spherical and derivative zeros**, [DLMF 10.58 prose](https://dlmf.nist.gov/10.58):
  a_(n,m),a′_(n,m),b_(n,m),b′_(n,m) denote the zeros of spherical j,j′,y,y′,
  counting0 as the first j′₀ zero. No named local families were found.
  The ordinary j/y zero families are related to half-integer cylinder zeros;
  the derivative zero families do not follow by simply changing the order
  index. Generic `DLMF.orderedZero` does not implement the special convention.

### §10.61 Definitions and Basic Properties

<!-- retained entry 81 -->
- **berν, beiν, kerν and keiν**, [10.61.1–2](https://dlmf.nist.gov/10.61.E1):
  no named Lean equivalents found. They are the real/imaginary components of
  the specified rotated J and K expressions, with real order and `x ≥ 0`.

### §10.63 Recurrence Relations and Derivatives

- **Kelvin cross-products**, [DLMF 10.63.E1](https://dlmf.nist.gov/10.63.E1),
  [10.63.E5](https://dlmf.nist.gov/10.63.E5):
  the permitted ordered pairs are (ber,bei),(bei,−ber),(ker,kei),(kei,−ker).
  For the first pair pν=ber²+bei²,qν=ber·bei′−ber′·bei,
  rν=ber·ber′+bei·bei′,sν=(ber′)²+(bei′)²; the ker/kei counterparts
  use the same definitions. No named local equivalents were found. These
  Kelvin p/q/r/s differ from the cylinder cross-products in 10.6.8.

### §10.68 Modulus and Phase Functions

<!-- retained entry 82 -->
- **Kelvin Mν, Nν, θν and φν**, [10.68.1–2 and branch prose](https://dlmf.nist.gov/10.68.i):
  no named equivalents found. The continuous phases are fixed by large-argument
  asymptotics; they are not simply principal arguments.

- **Continuous Kelvin phases**, [DLMF 10.68.E1–2 and prose](https://dlmf.nist.gov/10.68.i):
  Mν,Nν,θν,φν have the retained definitions and large-x normalization of their continuous phases. The Arctan formulas10.68.6 use the compatible continued
  branches, not the principal real arctangent alone. No named constructions
  were found. The exact lower-order asymptotic coefficients do not amount to
  a numerical definition of the functions.

### §10.69 Uniform Asymptotic Expansions for Large Order

- **Kelvin large-order coordinate**, [DLMF 10.69.E1](https://dlmf.nist.gov/10.69.E1):
  ξ=√(1+ix²), with principal fractional powers, is a complex expression
  without a separately named local object. Its Uₖ,Vₖ reuse10.41.

### §10.70 Zeros

- **Formal Kelvin zero-correction series**, [DLMF 10.70.E1–2](https://dlmf.nist.gov/10.70.E1):
  f(t) is the specified formal inverse-power series, beginning
  (μ−1)/(16t)+(μ−1)/(32t²),μ=4ν², and the four phase shifts t are
  explicitly fixed in 10.70.2. No named local formal series or indexed Kelvin
  zero family was found. This is an exact asymptotic object; the separate
  numerical evidence assigning m to a specific zero is not a proof or definition.

### §10.74 Methods of Computation

- **Spherical Bessel transform**, [DLMF 10.74.vii prose](https://dlmf.nist.gov/10.74.vii):
  the exact transform is the Hankel transform10.22.76 at half-odd-positive
  order. There is no extra named local transform object. This mathematical
  specialization is recorded even though its surrounding section discusses
  computation.

## Chapter 11 — Struve and related functions

Expanded review: all 16 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§11.1–11.16 checked; matching headings are §11.2,
§11.9(i), and §11.10(i).

### §11.2 Definitions

- **Struve normalized cores, logarithmic branches and equation predicates**, [DLMF 11.2](https://dlmf.nist.gov/11.2):
  The retained H,L,K,M constructions also have normalized entire `DLMF.Struve.struveHCore`, `DLMF.Struve.struveLCore`, reciprocal-Gamma `DLMF.Struve.struveCoeff`, and explicit logarithmic-plane `DLMF.Struve.struveHOnLog`, `DLMF.Struve.struveLOnLog` variants ([source](DLMF/Struve/Basic/Functions.lean#L27)). The ordinary/modified inhomogeneous equation is `DLMF.Struve.struveEquation`, with cleared `DLMF.Struve.besselResidual` and `DLMF.Struve.IsStruveSolutionOn`. The entire normalized series differs from the branch-dependent prefactor; principal powers alone do not record continuation through multiple turns.

<!-- retained entry 83 -->
- **Struve H and modified Struve L**, [11.2.1–2](https://dlmf.nist.gov/11.2.E1):
  `DLMF.Struve.struveH`, `struveL`, their entire cores `struveHCore`,
  `struveLCore`, and logarithmic versions `struveHOnLog`, `struveLOnLog`
  in [Basic](DLMF/Struve/Basic/Functions.lean#L31). The core removes the fractional
  power; `OnLog` records its sheet. These are genuine different constructions
  of the branch factor, not real/imaginary components.

<!-- retained entry 84 -->
- **Auxiliary Struve K and M**, [11.2.5–6](https://dlmf.nist.gov/11.2.E5):
  `DLMF.Struve.struveK`, `struveM` in
  [Basic](DLMF/Struve/Basic/Functions.lean#L61), the differences `H-Y` and `L-I`.
  Struve K is distinct from modified Bessel K. Its independently defined
  Laplace integral is `DLMF.Bessel.besselYLaplace` in
  [YIntegralRep](DLMF/Bessel/YIntegralRep.lean#L252), corresponding to
  [11.5.2](https://dlmf.nist.gov/11.5.E2) on the proper convergence domain.

<!-- retained entry 85 -->
- **Struve and modified Struve equations**, [11.2.7–10](https://dlmf.nist.gov/11.2.E7):
  `DLMF.Struve.struveEquation` and `IsStruveSolutionOn` in
  [Basic](DLMF/Struve/Basic/Functions.lean#L71), with a Boolean selecting the modified sign.

### §11.4 Basic Properties

- **Struve inequality constants and asymptotic coefficients**, [DLMF 11.4.ii](https://dlmf.nist.gov/11.4.ii):
  The bounds introducea₀ andμ₀ by the displayed ν-dependent maximum/minimum formulas; no independent local scalar wrapper was found. Half-integer Laurent coefficients are `DLMF.Struve.struveHalfCoeff`, `DLMF.Struve.struveHalfPoly` ([source](DLMF/Struve/Properties.lean#L232)). The large-orderAₖ(λ) of §11.6.8–9 are `DLMF.Struve.struveScaledCoeff` ([source](DLMF/Struve/Asymptotics/LargeOrder.lean#L462)); large-argument terms and finite remainders have explicit constructions in the asymptotic modules. Exact all-order coefficients remain in scope.

### §11.7 Integrals and Sums

- **Struve-H primitive**, [DLMF 11.7.E5](https://dlmf.nist.gov/11.7.E5):
  The straight-segment primitive based at zero of `t^ν H_ν(t)`, with the principal power used in
  the integrand.
  `DLMF.Struve.struveHPrimitive` ([definition](DLMF/Struve/Representations/BarnesAndSonine.lean#L261)).

### §11.9 Lommel Functions

<!-- retained entry 86 -->
- **Lommel denominator product aₖ and lower sμν**, [11.9.3–4](https://dlmf.nist.gov/11.9.E3):
  `DLMF.Struve.lommelA`, `lommelS`, and the parameter predicate `LommelRegular`
  in [Lommel](DLMF/Struve/Lommel.lean#L42).

- **Lommel product coefficients and removable parameter continuation**, [DLMF 11.9.E4](https://dlmf.nist.gov/11.9.E4):
  Aₖ(μ,ν) is `DLMF.Struve.lommelA`; `DLMF.Struve.LommelRegular` expresses the exclusions onμ±ν. There are `DLMF.Struve.lommelS`, `DLMF.Struve.lommelCapitalRegular`, and the distinct limit-filled `DLMF.Struve.lommelCapital` ([source](DLMF/Struve/Lommel.lean#L42)), together with the entire cancellation numerator. Their exact parameter-limit and differential-equation specifications are now proved, including simultaneous Gamma poles. The finite series and continued capital function must not be identified merely by totalizing denominators at excluded parameters.

<!-- retained entry 87 -->
- **Capital Lommel Sμν**, [11.9.5 and limiting-value prose](https://dlmf.nist.gov/11.9.E5):
  `DLMF.Struve.lommelCapitalRegular` and `lommelCapital` in
  [Lommel](DLMF/Struve/Lommel.lean#L57). The former is the connection formula;
  the latter chooses its parameter limit, including exceptional orders.

### §11.10 Anger–Weber Functions

<!-- retained entry 88 -->
- **Anger J and Weber E**, [11.10.1–2](https://dlmf.nist.gov/11.10.E1):
  `DLMF.Struve.angerJ`, `weberE` in
  [IntegralAndSeries](DLMF/Struve/AngerWeber/IntegralAndSeries.lean#L34),
  actual finite-interval integrals, entire in both complex arguments.

<!-- retained entry 89 -->
- **Associated Anger–Weber A**, [11.10.4](https://dlmf.nist.gov/11.10.E4):
  `DLMF.Struve.angerARegular` and `angerA` in
  [IntegralAndSeries](DLMF/Struve/AngerWeber/IntegralAndSeries.lean#L277).
  The quotient `(Anger J - Bessel J)/sin(πν)` is extended by order limits;
  the half-line integral is a bridge on its stated convergence domain.

- **Anger–Weber power series and finite half-integer auxiliaries**, [DLMF 11.10.E10](https://dlmf.nist.gov/11.10.E10):
  The retained Anger–Weber functions have additional constructions the two entire series `DLMF.Struve.angerS1`, `DLMF.Struve.angerS2` ([source](DLMF/Struve/AngerWeber/IntegralAndSeries.lean#L526)). The half-integer formulas introduce `DLMF.Struve.angerFresnelPlus`, `DLMF.Struve.angerFresnelMinus` and finite index counts `DLMF.Struve.weberM1`, `DLMF.Struve.weberM2` ([source](DLMF/Struve/AngerWeber/LommelConnections.lean#L117)); these encode the actual sum limits, including the empty case. In §11.11, even/odd productsFₖ,Gₖ are `DLMF.Struve.angerF`, `DLMF.Struve.angerG`; the scaled expansion has `DLMF.Struve.angerScaledA`, `DLMF.Struve.angerScaledB`, `DLMF.Struve.angerMu` ([source](DLMF/Struve/Asymptotics/AngerWeberExpansions.lean#L622)), and the Debye-polynomial family is `DLMF.Struve.angerDebyePoly` ([source](DLMF/Struve/Coefficients.lean#L26)). No new function family is introduced by §11.8's reference to Kelvin-type arguments.

  [DLMF 11.10.E10](https://dlmf.nist.gov/11.10.E10):
  The even entire Anger series with reciprocal-Gamma factors `Γ(k+ν/2+1)⁻¹ Γ(k-ν/2+1)⁻¹`.
  `DLMF.Struve.angerS1` ([definition](DLMF/Struve/AngerWeber/IntegralAndSeries.lean#L526)).

  [DLMF 11.10.E11](https://dlmf.nist.gov/11.10.E11):
  The odd entire Anger series with reciprocal-Gamma factors `Γ(k+ν/2+3/2)⁻¹ Γ(k-ν/2+3/2)⁻¹`.
  `DLMF.Struve.angerS2` ([definition](DLMF/Struve/AngerWeber/IntegralAndSeries.lean#L540)).

  [DLMF 11.10.E21](https://dlmf.nist.gov/11.10.E21):
  The sum of the complex Fresnel cosine and sine integrals used in half-integer Anger formulas.
  `DLMF.Struve.angerFresnelPlus` ([definition](DLMF/Struve/AngerWeber/LommelConnections.lean#L117)).

  [DLMF 11.10.E21](https://dlmf.nist.gov/11.10.E21):
  The difference of the complex Fresnel cosine and sine integrals used in half-integer Anger
  formulas.
  `DLMF.Struve.angerFresnelMinus` ([definition](DLMF/Struve/AngerWeber/LommelConnections.lean#L122)).

  [DLMF 11.10.E24](https://dlmf.nist.gov/11.10.E24):
  Number of terms floor((n-1)/2)+1, with empty case n=0. This is `(n+1)/2` in
  natural-number division (corrected 2026-10-20 from `n/2`, which gave no term at `n = 1`).
  `DLMF.Struve.weberM1` ([definition](DLMF/Struve/AngerWeber/LommelConnections.lean#L474)).

  [DLMF 11.10.E24](https://dlmf.nist.gov/11.10.E24):
  Number of terms ceil((n-3)/2)+1 for n positive.
  `DLMF.Struve.weberM2` ([definition](DLMF/Struve/AngerWeber/LommelConnections.lean#L480)).

### §11.11 Asymptotic Expansions of Anger–Weber Functions

- **Anger–Weber asymptotic auxiliary functions F and G**, [DLMF 11.11.E1](https://dlmf.nist.gov/11.11.E1):
  The product of the first `k` factors `ν²-(2j+1)²` in the even Anger asymptotic coefficients.
  `DLMF.Struve.angerF` ([definition](DLMF/Struve/Asymptotics/BinomialAndAnger.lean#L263)).

  [DLMF 11.11.E1](https://dlmf.nist.gov/11.11.E1):
  The product of the first `k` factors `ν²-(2j+2)²` in the odd Anger asymptotic coefficients.
  `DLMF.Struve.angerG` ([definition](DLMF/Struve/Asymptotics/BinomialAndAnger.lean#L268)).

- **Anger transition parameter μ**, [DLMF 11.11.E12](https://dlmf.nist.gov/11.11.E12):
  The principal-branch phase `√(1-lam²) - log ((1+√(1-lam²))/lam)` of the scaled Anger
  expansion.
  `DLMF.Struve.angerMu` ([definition](DLMF/Struve/Asymptotics/AngerWeberExpansions.lean#L735)).

## Chapter 12 — Parabolic cylinder functions

Expanded review: all 21 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§12.1–12.21 checked; no heading contains “Definition” or
“Definitions”. Complementary fundamental definitions are recorded here from
[§12.2](https://dlmf.nist.gov/12.2) and [§12.14](https://dlmf.nist.gov/12.14),
whose titles are “Differential Equations” and “The Function W(a,x)”.

### §12.2 Differential Equations

- **Parabolic-cylinder equations, U,V,D and their independent series**, [DLMF 12.2](https://dlmf.nist.gov/12.2):
  Chapter 12 places these fundamental definitions under equation/solution headings. `DLMF.Confluent.IsQuadraticCylinderSolution`, `DLMF.Confluent.IsOscillatoryCylinderSolution` ([source](DLMF/ParabolicCylinder/Basic/EquationAndPhaseData.lean#L22)) encode the quadratic-potential/oscillatory equations. The main U,V,D are `DLMF.Confluent.pcfU`, `DLMF.Confluent.pcfV`, `DLMF.Confluent.pcfD`, built from `DLMF.Confluent.pcfEven`, `DLMF.Confluent.pcfOdd` and their derivative formulas ([source](DLMF/ParabolicCylinder/Basic/Functions.lean#L24)); V's independent initial values/linear combination and `DLMF.Confluent.pcfVDeriv` are in [WronskiansAndConnections](DLMF/ParabolicCylinder/Basic/Functions.lean#L84). The Kummer representations and integral formulas are bridges for these constructions, with their branch restrictions.

  [DLMF 12.2.E1](https://dlmf.nist.gov/12.2.E1):
  The scalar quadratic-potential equation `f″(z) + (az²+bz+c)f(z) = 0`, written using totalized
  iterated derivatives.
  `DLMF.Confluent.IsQuadraticCylinderSolution` ([definition](DLMF/ParabolicCylinder/Basic/EquationAndPhaseData.lean#L22)).

  [DLMF 12.2.E3](https://dlmf.nist.gov/12.2.E3):
  The oscillatory Weber equation `f″(z) + (z²/4-a)f(z) = 0`, written using totalized iterated
  derivatives.
  `DLMF.Confluent.IsOscillatoryCylinderSolution` ([definition](DLMF/ParabolicCylinder/Basic/EquationAndPhaseData.lean#L28)).

<!-- retained entry 90 -->
- **U(a,z), Dν(z), and even/odd canonical solutions**, [12.2.2–5](https://dlmf.nist.gov/12.2.E2):
  `DLMF.Confluent.pcfU`, `pcfD`, `pcfEven`, `pcfOdd`, and their separately
  defined derivatives `pcfUDeriv`, `pcfEvenDeriv`, `pcfOddDeriv` in
  [EquationAndIntegrals](DLMF/ParabolicCylinder/Basic/Functions.lean#L24).
  The construction uses entire Kummer functions; integral representations
  are bridges on smaller parameter domains.

<!-- retained entry 91 -->
- **V(a,z)**, [§12.2(i), 12.2.8–9](https://dlmf.nist.gov/12.2.E8):
  `DLMF.Confluent.pcfV`, `pcfVDeriv`, `pcfVZero`, `pcfVDerivZero` in
  [WronskiansAndConnections](DLMF/ParabolicCylinder/Basic/Functions.lean#L71).

<!-- retained entry 92 -->
- **U-bar and modulus/phase F, θ, G, ψ**, [12.2.21–23](https://dlmf.nist.gov/12.2.E21):
  `DLMF.Confluent.pcfUBar`, `pcfUBarDeriv`, `pcfF`, `pcfTheta`,
  `pcfG`, and `pcfPsi` in [Basic](DLMF/ParabolicCylinder/Basic/EquationAndPhaseData.lean#L34).
  U-bar means a gamma-scaled V, not complex conjugation; its parameter poles
  are excluded in mathematical uses.

- **Barred cylinder solution and modulus/phase**, [DLMF 12.2.E21](https://dlmf.nist.gov/12.2.E21):
  Ubar=Γ(1/2−a)V is `DLMF.Confluent.pcfUBar`, with `DLMF.Confluent.pcfUBarDeriv`; it is undefined mathematically at the excluded positive half-integera, not complex conjugation. F,θ,G,ψ are `DLMF.Confluent.pcfF`, `DLMF.Confluent.pcfTheta`, `DLMF.Confluent.pcfG`, `DLMF.Confluent.pcfPsi` ([source](DLMF/ParabolicCylinder/Basic/EquationAndPhaseData.lean#L34)). The local phases use principal-argument representatives; a continuous phase lift differs by 2π multiples and should not be silently claimed identical globally.

### §12.7 Relations to Other Functions

- **Cylinder large-variable terms and repeated Gaussian tail**, [DLMF 12.7.E7](https://dlmf.nist.gov/12.7.E7):
  The hhₙ tail, including its Gaussian index −1 convention, is `DLMF.Confluent.hhFunction` ([source](DLMF/ParabolicCylinder/Relations.lean#L94)), a distinct normalization from repeated erfc in §7.18. The large-variable series terms are `DLMF.Confluent.pcfUTerm`, `DLMF.Confluent.pcfVTerm`, with logarithmic-sector `DLMF.Confluent.pcfLogWedge` ([source](DLMF/ParabolicCylinder/AsymptoticsZeros.lean#L25)); the comparable `DLMF.Confluent.pcfSect_uTerm`, `DLMF.Confluent.pcfSect_vTerm` implementations support the sector proofs. They are exact asymptotic terms, not convergent definitions of U,V everywhere.

  [DLMF 12.7.E7](https://dlmf.nist.gov/12.7.E7):
  The repeated Gaussian tail integral `∫₀∞ tⁿ/n! exp (-(z+t)²/2) dt`; the index `-1` denotes the
  Gaussian itself.
  `DLMF.Confluent.hhFunction` ([definition](DLMF/ParabolicCylinder/Relations.lean#L94)).

### §12.10 Uniform Asymptotic Expansions for Large Parameter

- **Olver cylinder phases, polynomials and normalizers**, [DLMF 12.10.E7](https://dlmf.nist.gov/12.10.E7):
  ξ,η,ξbar,h andΓ-coefficients are `DLMF.Confluent.pcfXi`, `DLMF.Confluent.pcfEta`, `DLMF.Confluent.pcfXiBar`, `DLMF.Confluent.pcfH`, `DLMF.Confluent.pcfGammaCoeff`. The recursively paired polynomialsuₛ,rₛ,vₛ are `DLMF.Confluent.pcfOlverPair`, `DLMF.Confluent.pcfOlverU`, `DLMF.Confluent.pcfOlverR`, `DLMF.Confluent.pcfOlverV` ([source](DLMF/ParabolicCylinder/Uniform/PhasesAndPolynomials.lean#L34)). Their exterior/interior/positive-parameter coefficient functions are `DLMF.Confluent.pcfOlverA`, `DLMF.Confluent.pcfOlverB`, `DLMF.Confluent.pcfOlverATilde`, `DLMF.Confluent.pcfOlverBTilde`, `DLMF.Confluent.pcfOlverUBar`, `DLMF.Confluent.pcfOlverVBar`, and oscillatory phases `DLMF.Confluent.pcfKappa`, `DLMF.Confluent.pcfChi` ([source](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L30)). `DLMF.Confluent.IsCylinderGNormalizer`, `DLMF.Confluent.IsCylinderGBarNormalizer` specify normalizer functions appearing existentially in expansion theorems; they do not select a unique namedg. `DLMF.Confluent.pcfUniformFilter` and `DLMF.Confluent.HasCylinderUniformExpansion` specify actual uniformity.

  [DLMF 12.10.E7](https://dlmf.nist.gov/12.10.E7):
  The exterior cylinder phase `(t√(t²-1) - log (t+√(t²-1)))/2` used in the exponential uniform
  expansion.
  `DLMF.Confluent.pcfXi` ([definition](DLMF/ParabolicCylinder/Uniform/PhasesAndPolynomials.lean#L34)).

  [DLMF 12.10.E8](https://dlmf.nist.gov/12.10.E8):
  The exterior uniform coefficient U divided by `(t²-1)^(3s/2)` on the principal complex branch.
  `DLMF.Confluent.pcfOlverA` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L30)).

  [DLMF 12.10.E8](https://dlmf.nist.gov/12.10.E8):
  The exterior derivative coefficient V divided by `(t²-1)^(3s/2)`.
  `DLMF.Confluent.pcfOlverB` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L46)).

  [DLMF 12.10.E11](https://dlmf.nist.gov/12.10.E11):
  The polynomial coefficient U of order `s` in the Olver recurrence for cylinder expansions.
  `DLMF.Confluent.pcfOlverU` ([definition](DLMF/ParabolicCylinder/Uniform/PhasesAndPolynomials.lean#L244)).

  [DLMF 12.10.E12](https://dlmf.nist.gov/12.10.E12):
  The auxiliary polynomial R paired with the next U coefficient in the Olver recurrence.
  `DLMF.Confluent.pcfOlverR` ([definition](DLMF/ParabolicCylinder/Uniform/PhasesAndPolynomials.lean#L249)).

  [DLMF 12.10.E13](https://dlmf.nist.gov/12.10.E13):
  The derivative coefficient polynomial V obtained from the Olver U and R families.
  `DLMF.Confluent.pcfOlverV` ([definition](DLMF/ParabolicCylinder/Uniform/PhasesAndPolynomials.lean#L254)).

  [DLMF 12.10.E14](https://dlmf.nist.gov/12.10.E14):
  The normalization condition for the negative-parameter cylinder expansion, with the prescribed
  Gamma coefficient series relative to `pcfH`.
  `DLMF.Confluent.IsCylinderGNormalizer` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L71)).

  [DLMF 12.10.E16](https://dlmf.nist.gov/12.10.E16):
  The `s`th asymptotic coefficient of the normalized half-shifted Gamma function that enters the
  cylinder normalizers.
  `DLMF.Confluent.pcfGammaCoeff` ([definition](DLMF/ParabolicCylinder/Uniform/PhasesAndPolynomials.lean#L57)).

  [DLMF 12.10.E22](https://dlmf.nist.gov/12.10.E22):
  The oscillatory cylinder phase `μ² η(t) - π/4`.
  `DLMF.Confluent.pcfKappa` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L84)).

  [DLMF 12.10.E22](https://dlmf.nist.gov/12.10.E22):
  The companion oscillatory cylinder phase `μ² η(t) + π/4`.
  `DLMF.Confluent.pcfChi` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L89)).

  [DLMF 12.10.E23](https://dlmf.nist.gov/12.10.E23):
  The interior cylinder phase `(arccos t - t√(1-t²))/2` used in the oscillatory uniform
  expansion.
  `DLMF.Confluent.pcfEta` ([definition](DLMF/ParabolicCylinder/Uniform/PhasesAndPolynomials.lean#L40)).

  [DLMF 12.10.E24](https://dlmf.nist.gov/12.10.E24):
  The interior uniform coefficient U divided by `(1-t²)^(3s/2)` on the principal complex branch.
  `DLMF.Confluent.pcfOlverATilde` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L35)).

  [DLMF 12.10.E24](https://dlmf.nist.gov/12.10.E24):
  The interior derivative coefficient V divided by `(1-t²)^(3s/2)`.
  `DLMF.Confluent.pcfOlverBTilde` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L51)).

  [DLMF 12.10.E26](https://dlmf.nist.gov/12.10.E26):
  The positive-parameter cylinder phase `(t√(t²+1) + log (t+√(t²+1)))/2`.
  `DLMF.Confluent.pcfXiBar` ([definition](DLMF/ParabolicCylinder/Uniform/PhasesAndPolynomials.lean#L46)).

  [DLMF 12.10.E27](https://dlmf.nist.gov/12.10.E27):
  The positive-parameter U coefficient obtained by substituting `-it` in the Olver polynomial
  and multiplying by `i^s`.
  `DLMF.Confluent.pcfOlverUBar` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L40)).

  [DLMF 12.10.E28](https://dlmf.nist.gov/12.10.E28):
  The positive-parameter cylinder normalizer condition, with the alternating Gamma coefficient
  expansion of `g(μ) μ√2 H(μ)`.
  `DLMF.Confluent.IsCylinderGBarNormalizer` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L101)).

  [DLMF 12.10.E30](https://dlmf.nist.gov/12.10.E30):
  The positive-parameter V coefficient obtained by substituting `-it` in the Olver polynomial
  and multiplying by `i^s`.
  `DLMF.Confluent.pcfOlverVBar` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L56)).

- **Temme and turning-point cylinder coefficients**, [DLMF 12.10.E32](https://dlmf.nist.gov/12.10.E32):
  The exterior coordinateτ is `DLMF.Confluent.pcfTau`; the modified polynomial recurrence is `DLMF.Confluent.pcfTemmePoly` with `DLMF.Confluent.pcfPolyPrimitive`. The signed Airy coordinateζ, its inverse and amplitudeφ are `DLMF.Confluent.pcfZeta`, `DLMF.Confluent.pcfInverseZeta`, `DLMF.Confluent.pcfPhi`. The Airy coefficient familiesαₛ,βₛ,Aₛ,Bₛ,Cₛ,Dₛ,χ are `DLMF.Confluent.pcfAiryAlpha`, `DLMF.Confluent.pcfAiryBeta`, `DLMF.Confluent.pcfAiryA`, `DLMF.Confluent.pcfAiryB`, `DLMF.Confluent.pcfAiryC`, `DLMF.Confluent.pcfAiryD`, `DLMF.Confluent.pcfAiryChi` ([source](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L204)). The removable t=1 branch and inverse coordinate are part of the intended definition. `DLMF.Confluent.HasCylinderAiryExpansion` records the expansion through turning-point zeros.

  [DLMF 12.10.E32](https://dlmf.nist.gov/12.10.E32):
  The auxiliary exterior coordinate `(t/√(t²-1)-1)/2` for the uniform cylinder coefficient
  recurrence.
  `DLMF.Confluent.pcfTau` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L110)).

  [DLMF 12.10.E39](https://dlmf.nist.gov/12.10.E39):
  The real Airy turning-point coordinate, positive for `t ≥ 1` and negative for `t < 1`, defined
  from the exterior and interior cylinder phases.
  `DLMF.Confluent.pcfZeta` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L204)).

  [DLMF 12.10.E40](https://dlmf.nist.gov/12.10.E40):
  The fourth-root amplitude in the cylinder Airy expansion, with its removable value `2^(-1/6)`
  at the turning point.
  `DLMF.Confluent.pcfPhi` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L489)).

  [DLMF 12.10.E42](https://dlmf.nist.gov/12.10.E42):
  Continuous coefficient at zero is supplied by a removable limit.
  `DLMF.Confluent.pcfAiryA` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L769)).

  [DLMF 12.10.E42](https://dlmf.nist.gov/12.10.E42):
  Continuous coefficient at zero is supplied by a removable limit.
  `DLMF.Confluent.pcfAiryB` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L782)).

  [DLMF 12.10.E43](https://dlmf.nist.gov/12.10.E43):
  The product-form Airy coefficient alpha used in the turning-point expansion of the cylinder
  functions.
  `DLMF.Confluent.pcfAiryAlpha` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L758)).

  [DLMF 12.10.E43](https://dlmf.nist.gov/12.10.E43):
  The companion Airy coefficient beta, expressed as `-(6m+1)/(6m-1)` times alpha.
  `DLMF.Confluent.pcfAiryBeta` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L764)).

  [DLMF 12.10.E45](https://dlmf.nist.gov/12.10.E45):
  The logarithmic derivative of the cylinder Airy amplitude `pcfPhi` in the zeta coordinate.
  `DLMF.Confluent.pcfAiryChi` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L821)).

  [DLMF 12.10.E46](https://dlmf.nist.gov/12.10.E46):
  Continuous coefficient at zero is supplied by a removable limit.
  `DLMF.Confluent.pcfAiryC` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L795)).

  [DLMF 12.10.E46](https://dlmf.nist.gov/12.10.E46):
  Continuous coefficient at zero is supplied by a removable limit.
  `DLMF.Confluent.pcfAiryD` ([definition](DLMF/ParabolicCylinder/Uniform/ExpansionData.lean#L808)).

### §12.11 Zeros

- **Cylinder zero coordinates and corrections**, [DLMF 12.11.E2](https://dlmf.nist.gov/12.11.E2):
  τₛ,λₛ are `DLMF.Confluent.pcfZeroTau`, `DLMF.Confluent.pcfZeroLambda` ([source](DLMF/ParabolicCylinder/AsymptoticsZeros.lean#L764)). Real zeros counted away from a turning point use `DLMF.Confluent.pcfDescendingZero`; the correction p₁ and exact first-zero coefficients are `DLMF.Confluent.pcfZeroP1`, `DLMF.Confluent.pcfFirstZeroCoeff` ([source](DLMF/ParabolicCylinder/TurningPoint.lean#L70)). The exact coefficients are used in place of treating rounded DLMF decimal displays as exact constants.

  [DLMF 12.11.E2](https://dlmf.nist.gov/12.11.E2):
  The leading complex phase coordinate for the `s`th large cylinder zero, including the
  logarithm of its Gamma connection coefficient.
  `DLMF.Confluent.pcfZeroTau` ([definition](DLMF/ParabolicCylinder/AsymptoticsZeros.lean#L764)).

  [DLMF 12.11.E3](https://dlmf.nist.gov/12.11.E3):
  The logarithmic correction `log (pcfZeroTau a s) - πi/2` in the expansion of the large
  cylinder zeros.
  `DLMF.Confluent.pcfZeroLambda` ([definition](DLMF/ParabolicCylinder/AsymptoticsZeros.lean#L770)).

  [DLMF 12.11.E6](https://dlmf.nist.gov/12.11.E6):
  The first correction in the cylinder turning-point zero expansion, defined by its removable
  limit in the uniform zeta coordinate.
  `DLMF.Confluent.pcfZeroP1` ([definition](DLMF/ParabolicCylinder/TurningPoint.lean#L79)).

  [DLMF 12.11.E9](https://dlmf.nist.gov/12.11.E9):
  Exact coefficients, rather than rounded decimals treated as exact asymptotic constants.
  `DLMF.Confluent.pcfFirstZeroCoeff` ([definition](DLMF/ParabolicCylinder/TurningPoint.lean#L110)).

### §12.14 The Function W ⁡ ( a , x )

- **Oscillatory Weber W and its coefficient/phase systems**, [DLMF 12.14](https://dlmf.nist.gov/12.14):
  The actual constructions include `DLMF.Confluent.pcfWZero`, `DLMF.Confluent.pcfWDerivZero`, `DLMF.Confluent.pcfWEven`, `DLMF.Confluent.pcfWOdd`, `DLMF.Confluent.pcfW`, `DLMF.Confluent.pcfWDeriv`, `DLMF.Confluent.pcfWK`, `DLMF.Confluent.pcfGammaPhase`, `DLMF.Confluent.pcfWRho` ([source](DLMF/ParabolicCylinder/Weber/Solutions.lean#L31)). The connection phase is a continuous Γ-phase normalized at 0, not an arbitrary principal argument. Power-series/asymptotic auxiliariesαₙ,βₙ,ω,S,s₁,s₂ and modulus/phase F,θ,G,ψ have actual `DLMF.Confluent.pcfWAlpha`, `DLMF.Confluent.pcfWBeta`, `DLMF.Confluent.pcfWOmega`, `DLMF.Confluent.pcfWS`, `DLMF.Confluent.pcfWCoeff`, `DLMF.Confluent.pcfWF`, `DLMF.Confluent.pcfWTheta`, `DLMF.Confluent.pcfWG`, `DLMF.Confluent.pcfWPsi` constructions ([source](DLMF/ParabolicCylinder/Weber/Representations.lean#L179)). Uniform phases σ,σbar andL are `DLMF.Confluent.pcfWSigma`, `DLMF.Confluent.pcfWSigmaBar`, `DLMF.Confluent.pcfWOlverL`, with `DLMF.Confluent.IsCylinderLNormalizer` ([source](DLMF/ParabolicCylinder/WeberUniform.lean#L42)). Bars on expansion data again denote transformed families, not conjugation.

  [DLMF 12.14.E5](https://dlmf.nist.gov/12.14.E5):
  The positive connection factor `√(1+exp(2πa)) - exp(πa)` for the real Weber function.
  `DLMF.Confluent.pcfWK` ([definition](DLMF/ParabolicCylinder/Weber/Solutions.lean#L241)).

  [DLMF 12.14.E6](https://dlmf.nist.gov/12.14.E6):
  The Weber connection phase `π/8` plus half the chosen Gamma phase.
  `DLMF.Confluent.pcfWRho` ([definition](DLMF/ParabolicCylinder/Weber/Solutions.lean#L346)).

  [DLMF 12.14.E7](https://dlmf.nist.gov/12.14.E7):
  Continuous argument of Gamma along the vertical line, normalized to zero at a=0.
  `DLMF.Confluent.pcfGammaPhase` ([definition](DLMF/ParabolicCylinder/Weber/Solutions.lean#L260)).

  [DLMF 12.14.E17](https://dlmf.nist.gov/12.14.E17):
  Combined exact amplitude s1+i s2, recovered from the two real W solutions.
  `DLMF.Confluent.pcfWS` ([definition](DLMF/ParabolicCylinder/Weber/Representations.lean#L565)).

  [DLMF 12.14.E19](https://dlmf.nist.gov/12.14.E19):
  The large-real-argument phase `x²/4 - a log x + π/4` plus half the Gamma phase.
  `DLMF.Confluent.pcfWOmega` ([definition](DLMF/ParabolicCylinder/Weber/Representations.lean#L538)).

  [DLMF 12.14.E22](https://dlmf.nist.gov/12.14.E22):
  The rising-factorial coefficient `(1/2+ia)_{2r}` in the large-argument Weber expansion.
  `DLMF.Confluent.pcfWCoeff` ([definition](DLMF/ParabolicCylinder/Weber/Representations.lean#L608)).

  [DLMF 12.14.E27](https://dlmf.nist.gov/12.14.E27):
  The exterior uniform Weber phase `μ² ξ(t) + π/4`.
  `DLMF.Confluent.pcfWSigma` ([definition](DLMF/ParabolicCylinder/WeberUniform.lean#L42)).

  [DLMF 12.14.E28](https://dlmf.nist.gov/12.14.E28):
  The rotated cylinder normalizer, including its exponential and Gamma-phase factors, used in
  the uniform Weber expansions.
  `DLMF.Confluent.pcfWOlverL` ([definition](DLMF/ParabolicCylinder/WeberUniform.lean#L52)).

  [DLMF 12.14.E29](https://dlmf.nist.gov/12.14.E29):
  The Weber normalizer expansion in reciprocal fourth powers of `μ`, with the first three
  coefficients fixed by DLMF normalization.
  `DLMF.Confluent.IsCylinderLNormalizer` ([definition](DLMF/ParabolicCylinder/WeberUniform.lean#L58)).

  [DLMF 12.14.E36](https://dlmf.nist.gov/12.14.E36):
  The positive-parameter uniform Weber phase `μ² ξBar(t) + π/4`.
  `DLMF.Confluent.pcfWSigmaBar` ([definition](DLMF/ParabolicCylinder/WeberUniform.lean#L47)).

  [DLMF 12.14.E37](https://dlmf.nist.gov/12.14.E37):
  The modulus of the normalized complex pair formed by `W(a,x)` and `W(a,-x)`.
  `DLMF.Confluent.pcfWF` ([definition](DLMF/ParabolicCylinder/Weber/Representations.lean#L713)).

  [DLMF 12.14.E37](https://dlmf.nist.gov/12.14.E37):
  The principal argument of the normalized complex Weber solution pair used to define its
  real-axis phase.
  `DLMF.Confluent.pcfWTheta` ([definition](DLMF/ParabolicCylinder/Weber/Representations.lean#L718)).

  [DLMF 12.14.E38](https://dlmf.nist.gov/12.14.E38):
  The modulus of the normalized pair of derivatives of `W(a,x)` and `W(a,-x)`.
  `DLMF.Confluent.pcfWG` ([definition](DLMF/ParabolicCylinder/Weber/Representations.lean#L744)).

  [DLMF 12.14.E38](https://dlmf.nist.gov/12.14.E38):
  The principal argument of the negated normalized derivative pair in the Weber modulus-phase
  representation.
  `DLMF.Confluent.pcfWPsi` ([definition](DLMF/ParabolicCylinder/Weber/Representations.lean#L749)).

<!-- retained entry 93 -->
- **W(a,x), initial values and canonical even/odd solutions**,
  [12.14.1–2](https://dlmf.nist.gov/12.14.E1),
  [12.14.8–10](https://dlmf.nist.gov/12.14.E8):
  `DLMF.Confluent.pcfW`, `pcfWZero`, `pcfWDerivZero`, `pcfWEven`,
  `pcfWOdd`, and `pcfWDeriv` in
  [Solutions](DLMF/ParabolicCylinder/Weber/Solutions.lean#L31).
  W has a real parameter and a complex argument; its series construction
  fixes DLMF's real normalization.

### §12.15 Generalized Parabolic Cylinder Functions

- **Generalized cylinder equation and parabolic coordinates**, [DLMF 12.15](https://dlmf.nist.gov/12.15):
  `DLMF.Confluent.IsGeneralizedCylinderSolution` ([source](DLMF/ParabolicCylinder/Basic/EquationAndPhaseData.lean#L63)) records the parameter-dependent generalized equation; no distinguished normalized solution is chosen there. The parabolic-cylinder coordinate substitution in §12.17 and paraboloid-of-revolution coordinates are geometric formulas used to separate the Helmholtz equation. No dedicated local coordinate chart was found. Methods, software and numerical approximations of §§12.18–21 do not add acquired functions.

  [DLMF 12.15.E1](https://dlmf.nist.gov/12.15.E1):
  The generalized cylinder equation with nonzero exponent parameter `lam`, evaluated at the
  specified argument.
  `DLMF.Confluent.IsGeneralizedCylinderSolution` ([definition](DLMF/ParabolicCylinder/Basic/EquationAndPhaseData.lean#L63)).

## Chapter 13 — Confluent hypergeometric functions

Expanded review: all 32 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§13.1–13.32 checked; matching sections are §13.2 and §13.14.

### §13.2 Definitions and Basic Properties

<!-- retained entry 94 -->
- **Kummer M = ₁F₁ and regularized M**, [13.2.2–4](https://dlmf.nist.gov/13.2.E2):
  `DLMF.Confluent.kummerM` in [Basic](DLMF/Confluent/Basic/KummerM.lean#L32),
  the ordinary series, and Mathlib `Complex.regularizedHGFun {a} {b} z`
  in [RegularizedHypergeometric](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean#L173).
  Ordinary M has exceptional lower parameters; the regularized series retains
  their removable values. The local ordinary series is not an analytic
  extension through those parameter poles.

<!-- retained entry 95 -->
- **Tricomi U**, [defining asymptotic 13.2.6](https://dlmf.nist.gov/13.2.E6):
  `DLMF.Confluent.kummerUConnection`, `kummerU`, and `kummerUOnLog` in
  [Basic](DLMF/Confluent/Basic/Tricomi.lean#L26). The principal U chooses order
  limits at integral b; the raw connection formula and the logarithmic
  formula represent U only for nonintegral b. Thus `OnLog` does not by itself
  supply integral-b continuation. U's half-line integral is a theorem representation.

### §13.5 Continued Fractions

- **Confluent continued fractions and large-parameter generating coefficients**, [DLMF 13.5](https://dlmf.nist.gov/13.5):
  Besides the main Kummer functions and their regularized/logarithmic variants, there are `DLMF.Confluent.kummerMContFractCoeff`, `DLMF.Confluent.kummerUContFractCoeff`, `DLMF.Confluent.kummerMContinuedFraction`, `DLMF.Confluent.kummerUContinuedFraction` ([source](DLMF/Confluent/ContinuedFractions.lean#L48)). The qₛ(z,a) generating function of 13.8.3 is `DLMF.Confluent.largeBGenerating`, `DLMF.Confluent.largeBCoeff` ([source](DLMF/Confluent/Asymptotics/LargeArgument.lean#L1093)). For13.8.11–16 the pₖ,qₖ,cₖ coefficient recurrences and Cν(a,ζ)=cos(πa)Jν(ζ)+sin(πa)Yν(ζ) are formula-defined objects without named local coefficient wrappers; the Bessel combination is an expression in the existing Bessel functions. The signedλ→ζ transition in 13.8(ii) is the same mathematical inversion relation as §8.12 with its own parameter normalization.

  [DLMF 13.5.E2](https://dlmf.nist.gov/13.5.E2):
  The continued fraction `1 + a₀z/(1 + a₁z/(1 + ⋯))` with the Kummer coefficients
  `kummerMContFractCoeff a b k` (DLMF 13.5.1).
  `DLMF.Confluent.kummerMContinuedFraction` ([definition](DLMF/Confluent/ContinuedFractions.lean#L57)).

  [DLMF 13.5.E4](https://dlmf.nist.gov/13.5.E4):
  The continued fraction `1 + u₀/z/(1 + u₁/z/(1 + ⋯))` with the Tricomi coefficients
  `kummerUContFractCoeff a b k` (DLMF 13.5.2).
  `DLMF.Confluent.kummerUContinuedFraction` ([definition](DLMF/Confluent/ContinuedFractions.lean#L73)).

### §13.6 Relations to Other Functions

- **Lower incomplete-Gamma integral for the Kummer reduction**, [DLMF 13.6.E5](https://dlmf.nist.gov/13.6.E5):
  Lower incomplete gamma via `₁F₁`, AAR §4.4:
  `γ(s,z) = z^s / s · M(s, s+1, -z)`.
  `DLMF.Confluent.lowerIncGamma` ([definition](DLMF/Confluent/Basic/IncompleteGamma.lean#L22)).

- **Real error-function integral for the Kummer reduction**, [DLMF 13.6.E7](https://dlmf.nist.gov/13.6.E7):
  The error function, entire in `z`, through the confluent series of AAR §4.4:
  `erf z = (2z/√π) M(1/2, 3/2, -z²)`. On the real line it is TauCeti's `TauCeti.Real.erf`
  (`erf_ofReal`).
  `DLMF.Confluent.erf` ([definition](DLMF/Confluent/Basic/ErrorFunctions.lean#L27)).

### §13.8 Asymptotic Approximations for Large Parameters

- **Large-b generating function and coefficient sequence**, [DLMF 13.8.E3](https://dlmf.nist.gov/13.8.E3):
  Analytic normalization of the generating function in 13.8.3.
  The former product of singular powers assigned zero at the removable point.
  `DLMF.Confluent.largeBGenerating` ([definition](DLMF/Confluent/Asymptotics/LargeArgument.lean#L1093)).

  [DLMF 13.8.E3](https://dlmf.nist.gov/13.8.E3):
  The `s`-th Taylor coefficient at `0` of `largeBGenerating a z`.
  `DLMF.Confluent.largeBCoeff` ([definition](DLMF/Confluent/Asymptotics/LargeArgument.lean#L1099)).

### §13.9 Zeros

- **Kummer zero sets and Bessel-series coefficients**, [DLMF 13.9](https://dlmf.nist.gov/13.9):
  Positive real zero sets are `DLMF.Confluent.kummerMPosZeros`, `DLMF.Confluent.kummerUPosZeros` ([source](DLMF/Confluent/Zeros/RealZeros.lean#L33)); the sector set for U is `DLMF.Confluent.kummerUSectorZeros` ([source](DLMF/Confluent/Zeros/ComplexZeros.lean#L528)). DLMF's N,T,P zero counts are cardinalities of these sets or expressions in theorem statements, not independent chosen zeros when no enumeration is supplied. The coefficients Aₙ of 13.11.4 have the actual recurrence `DLMF.Confluent.besselExpansionCoeff` ([source](DLMF/Confluent/Series.lean#L297)). The parabolic zero-exclusion region in 13.9 is an explicit set predicate; its interpretation requires the stated real parameters.

### §13.11 Series

- **Kummer–Bessel expansion coefficients**, [DLMF 13.11.E4](https://dlmf.nist.gov/13.11.E4):
  Coefficients `A_s` in DLMF 13.11.3–13.11.4.
  `DLMF.Confluent.besselExpansionCoeff` ([definition](DLMF/Confluent/Series.lean#L297)).

### §13.14 Definitions and Basic Properties

- **Whittaker variants, continued fractions and Buchholz coefficients**, [DLMF 13.14](https://dlmf.nist.gov/13.14):
  The actual `DLMF.Confluent.regularizedWhittakerM`, `DLMF.Confluent.whittakerMOnLog`, `DLMF.Confluent.whittakerWOnLog` ([source](DLMF/Confluent/Whittaker.lean#L34)) supplement the retained ordinary M,W. The regularized M continues across lower-parameter poles, while ordinary M/Gamma totalization need not do so. Whittaker continued fractions and their coefficients are `DLMF.Confluent.whittakerMContFractCoeff`, `DLMF.Confluent.whittakerWContFractCoeff`, `DLMF.Confluent.whittakerMContinuedFraction`, `DLMF.Confluent.whittakerWContinuedFraction` ([source](DLMF/Confluent/ContinuedFractions.lean#L848)). The polynomials pₛ^(μ)(z) of 13.24.3 are `DLMF.Confluent.whittakerBesselGenerating`, `DLMF.Confluent.whittakerBesselCoeff` ([source](DLMF/Confluent/Basic/Buchholz.lean#L28)), defined by analytic Taylor coefficients of a removable generating function; the Bessel representation theorem is separate. The parameter-dependent implicit coordinates and envelopes in §§13.20–21 are expressed by equations/existential variables; no general selected local coordinate construction was identified. The paraboloidal coordinates in §13.28 are descriptive application substitutions.

<!-- retained entry 96 -->
- **Whittaker M and W**, [13.14.2–3](https://dlmf.nist.gov/13.14.E2):
  `DLMF.Confluent.whittakerM`, `whittakerW`, `whittakerMOnLog`, and
  `whittakerWOnLog` in [Whittaker](DLMF/Confluent/Whittaker.lean#L29).
  Principal W uses the continued U. The logarithmic W connection expression
  requires `2μ` nonintegral; it is not the full continuation at half-integer μ.

<!-- retained entry 97 -->
- **Regularized Whittaker M**, [limiting normalization 13.14.7](https://dlmf.nist.gov/13.14.E7):
  `DLMF.Confluent.regularizedWhittakerM` in
  [Whittaker](DLMF/Confluent/Whittaker.lean#L34), using the regularized series
  before multiplication. It is different from dividing totalized ordinary M
  by gamma at exceptional parameters.

### §13.17 Continued Fractions

- **Whittaker-M continued fraction**, [DLMF 13.17.E2](https://dlmf.nist.gov/13.17.E2):
  The continued fraction with the Whittaker `M` coefficients `whittakerMContFractCoeff κ μ k`
  (DLMF 13.17.1).
  `DLMF.Confluent.whittakerMContinuedFraction` ([definition](DLMF/Confluent/ContinuedFractions.lean#L857)).

- **Whittaker-W continued fraction**, [DLMF 13.17.E4](https://dlmf.nist.gov/13.17.E4):
  The continued fraction with the Whittaker `W` coefficients `whittakerWContFractCoeff κ μ k`
  (DLMF 13.17.3).
  `DLMF.Confluent.whittakerWContinuedFraction` ([definition](DLMF/Confluent/ContinuedFractions.lean#L873)).

### §13.24 Series

- **Whittaker–Bessel generating function and coefficients**, [DLMF 13.24.E3](https://dlmf.nist.gov/13.24.E3):
  Generating function for `p_s^{(μ)}(z)` in DLMF 13.24.3.
  `DLMF.Confluent.whittakerBesselGenerating` ([definition](DLMF/Confluent/Basic/Buchholz.lean#L28)).

  [DLMF 13.24.E3](https://dlmf.nist.gov/13.24.E3):
  The coefficient `p_s^{(μ)}(z) (-z)^s` of the Bessel expansion of Whittaker's `M` (DLMF 13.24.3),
  the `s`-th Taylor coefficient at `0` of the generating function times `(-z)^s`.
  `DLMF.Confluent.whittakerBesselCoeff` ([definition](DLMF/Confluent/Basic/Buchholz.lean#L34)).

## Chapter 14 — Legendre and related functions

Expanded review: all 34 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§14.1–14.34 checked; matching headings are §14.3,
§14.20(i), §14.21, and §14.30(i).

### §14.3 Definitions and Hypergeometric Representations

<!-- retained entry 98 -->
- **Ferrers P**, [14.3.1](https://dlmf.nist.gov/14.3.E1):
  `DLMF.Legendre.ferrersP` in [Basic](DLMF/Legendre/Basic/Functions.lean#L28), with
  real argument in `(-1,1)` and complex degree/order. The polynomial
  specialization `ferrersPNat` in [Harmonics](DLMF/Legendre/Harmonics.lean#L29)
  is independently defined by derivatives of the Legendre polynomial.

<!-- retained entry 99 -->
- **Ferrers Q and auxiliary w₁,w₂**, [14.3.2](https://dlmf.nist.gov/14.3.E2),
  [14.3.13–14](https://dlmf.nist.gov/14.3.E13):
  `DLMF.Legendre.ferrersQ`, `ferrersW1`, `ferrersW2` in
  [QuadraticFerrers](DLMF/Legendre/Associated/QuadraticFerrers.lean#L54).
  The quadratic hypergeometric construction avoids division by `sin(πμ)`
  at integer orders. `LegendreQRegular` records the excluded `ν+μ` values.

<!-- retained entry 101 -->
- **Olver's regularized hypergeometric F-bold**, [14.3.3](https://dlmf.nist.gov/14.3.E3):
  `DLMF.Hypergeometric.regularizedGaussHG`, as detailed in Chapter 15.

- **Classical Gauss function on its principal cut plane at regular c. This is a**, [DLMF 14.3.E3](https://dlmf.nist.gov/14.3.E3):
  Classical Gauss function on its principal cut plane at regular c. This is a
  continuation, not the totalized power series outside its convergence disk.
  `DLMF.Legendre.legendreGaussF` ([definition](DLMF/Legendre/Hypergeometric.lean#L26)).

<!-- retained entry 100 -->
- **Associated Legendre P, Q and Olver Q-bold**,
  [14.3.6–10](https://dlmf.nist.gov/14.3.E6) and
  [complex continuation prose in §14.21(i)](https://dlmf.nist.gov/14.21.i):
  `DLMF.Legendre.associatedP`, `associatedQ`, `olverQ`, and branch factor
  `legendreBranchPower` in
  [QuadraticFerrers](DLMF/Legendre/Associated/QuadraticFerrers.lean#L28).
  Q-bold is regularized before multiplication by `Gamma(ν+μ+1)`; it remains
  meaningful where classical Q has parameter poles. Separate logarithms of
  `z-1` and `z+1` preserve continuation from `z > 1` on the DLMF cut.
  The order-zero functions `legendreP` in [Basic](DLMF/Legendre/Basic/Functions.lean#L23)
  and `legendreQ` in [SecondKind](DLMF/Legendre/SecondKind.lean#L105)
  are separate definitions with their own representations.

### §14.7 Integer Degree and Order

- **Integer-degree Legendre auxiliary polynomials and integral variables**, [DLMF 14.7](https://dlmf.nist.gov/14.7):
  Besides the retained P,Q,Ferrers/associated/Olver-normalized variants, the polynomial Wₙ occurring in the integer-degreeQ formula and the coefficientaₙ of degree differentiation in 14.11.3 are exact auxiliaries (the latter `DLMF.Legendre.legendreDegreeA` in [Hypergeometric](DLMF/Legendre/Hypergeometric.lean#L569)). The variable U of 14.12.10 is `DLMF.Legendre.legendreUCoordinate` ([source](DLMF/Legendre/IntegralRepresentations/Ferrers.lean#L388)). Continued-fraction numerators/denominators are `DLMF.Legendre.legendrePCFNum`, `DLMF.Legendre.legendrePCFDen`, `DLMF.Legendre.legendreQCFNum`, `DLMF.Legendre.legendreQCFDen` ([source](DLMF/Legendre/Series.lean#L940)). These ratios remain subject to their non-simultaneous-zero conditions.

### §14.11 Derivatives with Respect to Degree or Order

- **Legendre degree-derivative auxiliary function A**, [DLMF 14.11.E3](https://dlmf.nist.gov/14.11.E3):
  DLMF 14.11.3: the function `𝖠^μ_ν(x) = sin(νπ) ((1+x)/(1-x))^{μ/2} Σ_{k≥0} ((1-x)/2)^k Γ(k-ν)
  Γ(k+ν+1)/(k! Γ(k-μ+1)) (ψ(k+ν+1) - ψ(k-ν))` (as a `tsum`) appearing in the degree derivatives
  14.11.1–2.
  `DLMF.Legendre.legendreDegreeA` ([definition](DLMF/Legendre/Hypergeometric.lean#L569)).

### §14.12 Integral Representations

- **Legendre integral coordinate u**, [DLMF 14.12.E10](https://dlmf.nist.gov/14.12.E10):
  DLMF 14.12.10: the upper limit `u = ½ ln((x+1)/(x−1))` (for `x > 1`) used in 14.12.9 and in the
  uniform expansions of 14.15(ii).
  `DLMF.Legendre.legendreUCoordinate` ([definition](DLMF/Legendre/IntegralRepresentations/Ferrers.lean#L388)).

### §14.14 Continued Fractions

- **Continued-fraction numerator and denominator for Legendre P**, [DLMF 14.14.E2](https://dlmf.nist.gov/14.14.E2):
  DLMF 14.14.2: the partial numerators `(ν−μ−k+1)(ν+μ+k)(x²−1)/4` of the continued fraction
  14.14.1 for `P^μ_ν(x)`.
  `DLMF.Legendre.legendrePCFNum` ([definition](DLMF/Legendre/Series.lean#L940)).

  [DLMF 14.14.E2](https://dlmf.nist.gov/14.14.E2):
  DLMF 14.14.2: the partial denominators `(μ+k) x` of the continued fraction 14.14.1 for
  `P^μ_ν(x)`.
  `DLMF.Legendre.legendrePCFDen` ([definition](DLMF/Legendre/Series.lean#L946)).

- **Continued-fraction numerator and denominator for Legendre Q**, [DLMF 14.14.E4](https://dlmf.nist.gov/14.14.E4):
  DLMF 14.14.4: the partial numerators of the continued fraction 14.14.3 for `Q^μ_ν(x)`: `1` at `k
  = 0` and `−(ν+μ+k)(ν−μ+k)` for `k ≥ 1`.
  `DLMF.Legendre.legendreQCFNum` ([definition](DLMF/Legendre/Series.lean#L952)).

  [DLMF 14.14.E4](https://dlmf.nist.gov/14.14.E4):
  DLMF 14.14.4: the partial denominators `(2ν+2k+1) x` of the continued fraction 14.14.3 for
  `Q^μ_ν(x)`.
  `DLMF.Legendre.legendreQCFDen` ([definition](DLMF/Legendre/Series.lean#L958)).

### §14.15 Uniform Asymptotic Approximations

- **Legendre uniform asymptotic coordinates and envelopes**, [DLMF 14.15](https://dlmf.nist.gov/14.15):
  The large-orderα,p,ρ,η are `DLMF.Legendre.legendreOrderAlpha`, `DLMF.Legendre.legendreOrderP`, `DLMF.Legendre.legendreOrderRho`, `DLMF.Legendre.LegendreEtaRelation`, `DLMF.Legendre.legendreOrderEta`; the large-degreeα,β,y are `DLMF.Legendre.legendreDegreeAlpha`, `DLMF.Legendre.legendreDegreeBeta`, `DLMF.Legendre.LegendreYRelation`, `DLMF.Legendre.legendreDegreeY` ([source](DLMF/Legendre/UniformCoordinates/TurningPointMaps.lean#L35)). The defining relation includes sign conditions selecting the right branch ofy. Cylinder envelopes/crossing point anda,α,y coordinates are `DLMF.Legendre.cylinderEnvelopeCross`, `DLMF.Legendre.legendreCylinderEnvelope`, `DLMF.Legendre.legendreCylinderA`, `DLMF.Legendre.legendreCylinderAlpha`, `DLMF.Legendre.LegendreCylinderRelation` with the selected inverse-coordinate constructions ([source](DLMF/Legendre/UniformCoordinates/InverseCoordinates.lean#L225)). A relation plus a choice requires its existence/uniqueness theorem; the numerical example in the historical correction is not a definition. Integer/fractional degree/order parts in 14.16 are `DLMF.Legendre.legendreIntegerPart`, `DLMF.Legendre.legendreFractionalPart` ([source](DLMF/Legendre/Zeros/FerrersAndReal.lean#L31)).

  [DLMF 14.15.E5](https://dlmf.nist.gov/14.15.E5):
  DLMF 14.15.5: the ratio `α = (ν+1/2)/μ` used in the large-order uniform expansions
  14.15.4–14.15.10.
  `DLMF.Legendre.legendreOrderAlpha` ([definition](DLMF/Legendre/UniformCoordinates/TurningPointMaps.lean#L35)).

  [DLMF 14.15.E6](https://dlmf.nist.gov/14.15.E6):
  DLMF 14.15.6: the auxiliary variable `p = x/(α²x² + 1 − α²)^{1/2}` of the large-order expansion
  14.15.4.
  `DLMF.Legendre.legendreOrderP` ([definition](DLMF/Legendre/UniformCoordinates/TurningPointMaps.lean#L41)).

  [DLMF 14.15.E7](https://dlmf.nist.gov/14.15.E7):
  DLMF 14.15.7: the exponent `ρ = ½ ln((1+p)/(1−p)) + (α/2) ln((1−αp)/(1+αp))`, with `p` from
  14.15.6, of the large-order expansion 14.15.4.
  `DLMF.Legendre.legendreOrderRho` ([definition](DLMF/Legendre/UniformCoordinates/TurningPointMaps.lean#L47)).

  [DLMF 14.15.E10](https://dlmf.nist.gov/14.15.E10):
  DLMF 14.15.10: the relation `α ln((α²+η²)^{1/2} + α) − α ln η − (α²+η²)^{1/2} = ½ ln(((1+α²)x² +
  1 − α² − 2x(α²x² − α² + 1)^{1/2})/((x²−1)(1−α²))) + (α/2) ln((α²(2x²−1) + 1 + 2αx(α²x² − α² +
  1)^{1/2})/(1−α²))` defining `η` in 14.15.8–14.15.9.
  `DLMF.Legendre.LegendreEtaRelation` ([definition](DLMF/Legendre/UniformCoordinates/TurningPointMaps.lean#L53)).

  [DLMF 14.15.E10](https://dlmf.nist.gov/14.15.E10):
  DLMF 14.15.10: the variable `η`, chosen as a positive solution of `LegendreEtaRelation α x η`
  (unique for `0 ≤ α < 1`, `x > 1`; see `legendreOrderEta_spec`).
  `DLMF.Legendre.legendreOrderEta` ([definition](DLMF/Legendre/UniformCoordinates/TurningPointMaps.lean#L60)).

  [DLMF 14.15.E19](https://dlmf.nist.gov/14.15.E19):
  DLMF 14.15.19: the ratio `α = μ/(ν+1/2)` used in the large-degree uniform expansions
  14.15.15–14.15.22.
  `DLMF.Legendre.legendreDegreeAlpha` ([definition](DLMF/Legendre/UniformCoordinates/TurningPointMaps.lean#L402)).

  [DLMF 14.15.E20](https://dlmf.nist.gov/14.15.E20):
  DLMF 14.15.20: the normalizing factor `β = e^μ ((ν−μ+1/2)/(ν+μ+1/2))^{ν/2+1/4} ((ν+1/2)² −
  μ²)^{−μ/2}` of the large-degree expansions 14.15.15–14.15.18.
  `DLMF.Legendre.legendreDegreeBeta` ([definition](DLMF/Legendre/UniformCoordinates/TurningPointMaps.lean#L408)).

  [DLMF 14.15.E21](https://dlmf.nist.gov/14.15.E21):
  LegendreYRelation. For `x ≥ √(1−α²)` the equation 14.15.22 has a root in `(0, α²)` and one
  in `(−∞, 0)` whenever its right side is negative; DLMF's `y` decreases through `0` at `x = 1`, so the
  sign conditions `x < 1 → 0 < y` and `1 < x → y < 0` select it (corrected 2026-10-22; at `α = 0.6`,
  `x = 0.9` both `y = 0.177237` and `y = −0.116411` solve the equation).
  `DLMF.Legendre.LegendreYRelation` ([definition](DLMF/Legendre/UniformCoordinates/TurningPointMaps.lean#L414)).

  [DLMF 14.15.E23](https://dlmf.nist.gov/14.15.E23):
  DLMF 14.15.23: the crossing point `X_c`, the largest positive root of `U(−c, x) = Ū(−c, x)`,
  that separates the two branches of the parabolic-cylinder envelopes.
  `DLMF.Legendre.cylinderEnvelopeCross` ([definition](DLMF/Legendre/UniformCoordinates/InverseCoordinates.lean#L225)).

  [DLMF 14.15.E23](https://dlmf.nist.gov/14.15.E23):
  DLMF 14.15.23: the envelope functions `env U(−c, x)` (or `env Ū(−c, x)` when `barred`),
  equal to `(U(−c,x)² + Ū(−c,x)²)^{1/2}` for `x ≤ X_c` and to `√2 U(−c,x)` (resp. `√2 Ū(−c,x)`)
  for `x > X_c`.
  `DLMF.Legendre.legendreCylinderEnvelope` ([definition](DLMF/Legendre/UniformCoordinates/InverseCoordinates.lean#L231)).

  [DLMF 14.15.E26](https://dlmf.nist.gov/14.15.E26):
  DLMF 14.15.26: the turning-point parameter `a = ((ν+μ+1/2)|ν−μ+1/2|)^{1/2}/(ν+1/2)` of the
  parabolic-cylinder expansions 14.15.24–14.15.31.
  `DLMF.Legendre.legendreCylinderA` ([definition](DLMF/Legendre/UniformCoordinates/InverseCoordinates.lean#L238)).

  [DLMF 14.15.E26](https://dlmf.nist.gov/14.15.E26):
  DLMF 14.15.26: the parameter `α = (2|ν−μ+1/2|/(ν+1/2))^{1/2}` of the parabolic-cylinder
  expansions 14.15.24–14.15.31.
  `DLMF.Legendre.legendreCylinderAlpha` ([definition](DLMF/Legendre/UniformCoordinates/InverseCoordinates.lean#L244)).

  [DLMF 14.15.E27](https://dlmf.nist.gov/14.15.E27):
  DLMF 14.15.27–14.15.29, 14.15.31: the relation between `x` and `ζ` defining the
  parabolic-cylinder variable, with branches for `a = 0` (`ζ² = −ln(1−x²)`, `xζ ≥ 0`), for `μ ≤ ν+1/2`
  with `x ≥ a` (14.15.27) or `|x| < a` (14.15.28), and for `μ > ν+1/2` (14.15.31).
  `DLMF.Legendre.LegendreCylinderRelation` ([definition](DLMF/Legendre/UniformCoordinates/InverseCoordinates.lean#L250)).

### §14.16 Zeros

- **Legendre zero-count integer and fractional parts**, [DLMF 14.16.E1](https://dlmf.nist.gov/14.16.E1):
  DLMF 14.16.1: the integer part `⌊μ⌋` of the order `μ`, so that `μ = ⌊μ⌋ + δ_μ` with `0 ≤ δ_μ <
  1`.
  `DLMF.Legendre.legendreIntegerPart` ([definition](DLMF/Legendre/Zeros/FerrersAndReal.lean#L31)).

  [DLMF 14.16.E1](https://dlmf.nist.gov/14.16.E1):
  DLMF 14.16.1: the fractional part `δ_μ = μ - ⌊μ⌋`.
  `DLMF.Legendre.legendreFractionalPart` ([definition](DLMF/Legendre/Zeros/FerrersAndReal.lean#L37)).

### §14.17 Integrals

- **Primitive for a product of Ferrers functions**, [DLMF 14.17.E3](https://dlmf.nist.gov/14.17.E3):
  DLMF 14.17.3 and 14.17.4: the closed-form primitive built from `F, G` at degrees `ν` and `ν+1`;
  for Ferrers solutions it is an antiderivative of `x F G` (`singular = false`, requires `ν ≠ 0, -1`)
  or of `x (1-x²)^{-3/2} F G` (`singular = true`).
  `DLMF.Legendre.ferrersProductPrimitive` ([definition](DLMF/Legendre/Primitives.lean#L131)).

### §14.19 Toroidal (or Ring) Functions

- **Toroidal coordinates and conical transformation data**, [DLMF 14.19.E1](https://dlmf.nist.gov/14.19.E1):
  The toroidal chart is `DLMF.Legendre.toroidalCoordinates` ([source](DLMF/Legendre/Toroidal.lean#L24)); toroidal/ring functions are the indicated half-integer-degree Legendre solutions, with the existing normalizations rather than a new independent differential equation. The conical family also has `DLMF.Legendre.mehlerFockTransform`, `DLMF.Legendre.mehlerFockInverse` ([source](DLMF/Legendre/Conical.lean#L555)) and `DLMF.Legendre.conicalAlpha`, `DLMF.Legendre.conicalSigma`, `DLMF.Legendre.ConicalEtaRelation`, `DLMF.Legendre.conicalEta`, `DLMF.Legendre.conicalBeta`, `DLMF.Legendre.conicalRho` ([source](DLMF/Legendre/ConicalAsymptotics.lean#L41)). These are exact integral transforms and transition variables, with principal inverse-trigonometric branches.

  [DLMF 14.19.E1](https://dlmf.nist.gov/14.19.E1):
  DLMF 14.19.1: the toroidal coordinates map `(η, θ, φ) ↦ (x, y, z) = (c sinh η cos φ, c sinh η
  sin φ, c sin θ)/(cosh η - cos θ)`.
  `DLMF.Legendre.toroidalCoordinates` ([definition](DLMF/Legendre/Toroidal.lean#L24)).

### §14.20 Conical (or Mehler) Functions

<!-- retained entry 102 -->
- **Conical/Mehler functions and Dunster Q-hat**, [14.20.1–3](https://dlmf.nist.gov/14.20.E1):
  `DLMF.Legendre.conicalP` and `conicalQHat` in
  [Conical](DLMF/Legendre/Conical.lean#L24). Parameters are ordered `τ, μ, x`,
  with degree `-1/2+iτ` and order `-μ`. Q-hat excludes `τ=0` with positive
  half-odd-integral μ. For `x > 1`, the conical solution is instead the
  specialization of `associatedP`, not the Ferrers wrapper.

- **Mehler–Fock integral transform**, [DLMF 14.20.E11](https://dlmf.nist.gov/14.20.E11):
  DLMF 14.20.11: the generalized Mehler–Fock transform `f(τ) = (τ/π) sinh(τπ) Γ(1/2-μ+iτ)
  Γ(1/2-μ-iτ) ∫₁^∞ P^μ_{-1/2+iτ}(x) g(x) dx`, taken as an improper integral at `+∞`.
  `DLMF.Legendre.mehlerFockTransform` ([definition](DLMF/Legendre/Conical.lean#L555)).

- **Inverse Mehler–Fock integral transform**, [DLMF 14.20.E12](https://dlmf.nist.gov/14.20.E12):
  DLMF 14.20.12: the inverse Mehler–Fock transform `g(x) = ∫₀^∞ P^μ_{-1/2+iτ}(x) f(τ) dτ`, taken
  as an improper integral at `+∞`.
  `DLMF.Legendre.mehlerFockInverse` ([definition](DLMF/Legendre/Conical.lean#L561)).

- **Conical transition parameter α**, [DLMF 14.20.E19](https://dlmf.nist.gov/14.20.E19):
  DLMF 14.20.19: the ratio `α = μ/τ` used in the uniform large-`τ` asymptotics of conical
  functions.
  `DLMF.Legendre.conicalAlpha` ([definition](DLMF/Legendre/ConicalAsymptotics.lean#L41)).

- **Conical transition parameter σ**, [DLMF 14.20.E20](https://dlmf.nist.gov/14.20.E20):
  DLMF 14.20.20: the normalizing factor `σ(μ, τ) = exp(μ - τ arctan(μ/τ))/(μ²+τ²)^{μ/2}` of the
  uniform large-`τ` conical-function asymptotics.
  `DLMF.Legendre.conicalSigma` ([definition](DLMF/Legendre/ConicalAsymptotics.lean#L47)).

- **Implicit conical transition coordinates η and ψ**, [DLMF 14.20.E21](https://dlmf.nist.gov/14.20.E21):
  DLMF 14.20.21: the relation `√(α²+η) + (α/2) ln η - α ln(√(α²+η) + α) = arccos(x/√(1+α²)) +
  (α/2) ln((1+α²+(α²-1)x² - 2αx√(1+α²-x²))/((1+α²)(1-x²)))` defining the variable `η` of the uniform
  conical-function asymptotics.
  `DLMF.Legendre.ConicalEtaRelation` ([definition](DLMF/Legendre/ConicalAsymptotics.lean#L53)).

  [DLMF 14.20.E21](https://dlmf.nist.gov/14.20.E21):
  DLMF 14.20.21: the variable `η(α, x)`, chosen as a positive solution of the relation
  `ConicalEtaRelation α x η` (and characterized as the unique one by `conicalEta_spec`).
  `DLMF.Legendre.conicalEta` ([definition](DLMF/Legendre/ConicalAsymptotics.lean#L60)).

- **Conical transition parameter β**, [DLMF 14.20.E23](https://dlmf.nist.gov/14.20.E23):
  DLMF 14.20.23: the ratio `β = τ/μ` used in the uniform large-`μ` asymptotics of conical
  functions.
  `DLMF.Legendre.conicalBeta` ([definition](DLMF/Legendre/ConicalAsymptotics.lean#L365)).

- **Conical transition parameter ρ**, [DLMF 14.20.E24](https://dlmf.nist.gov/14.20.E24):
  DLMF 14.20.24: the variable `ρ(β, x) = (1/2) ln(((1-β²)x² + 1 + β² + 2x√(1+β²-β²x²))/(1-x²)) + β
  arctan(βx/√(1+β²-β²x²)) - (1/2) ln(1+β²)` of the uniform conical-function asymptotics.
  `DLMF.Legendre.conicalRho` ([definition](DLMF/Legendre/ConicalAsymptotics.lean#L371)).

### §14.24 Analytic Continuation

- **Continued Legendre branches and generalized equation**, [DLMF 14.24](https://dlmf.nist.gov/14.24):
  P(z,s),Q(z,s) and the subscript-s branches record the two specified circuit families around±1. `DLMF.Legendre.legendreTransport` ([source](DLMF/Legendre/Continuation/LogarithmicBranches.lean#L695)), `DLMF.Legendre.legendreEllipsePath` ([source](DLMF/Legendre/Continuation/LogarithmicBranches.lean#L830)), `DLMF.Legendre.legendreEllipseContinued` ([source](DLMF/Legendre/Continuation/LogarithmicBranches.lean#L834)), `DLMF.Legendre.legendreOneLoop` ([source](DLMF/Legendre/Continuation/Monodromy.lean#L423)), `DLMF.Legendre.legendreOneContinued` ([source](DLMF/Legendre/Continuation/Monodromy.lean#L427)) construct the path transport and circuit representatives; principal P,Q alone carry no circuit number. `DLMF.Legendre.IsGeneralizedLegendreSolution` ([source](DLMF/Legendre/Associated/BoundaryAndConnections.lean#L635)) records §14.29's generalized equation. Spheroidal surface harmonic names and normalized oblate variants in §14.30 are distinct from general homogeneous harmonic polynomials; the actual harmonic wrappers are listed at §14.30. The angular-momentum operators L²,L_z defined in §14.30(iv) are descriptive differential-operator formulas; no project-local physics-operator construction was found.

### §14.29 Generalizations

- **Generalized Legendre equation predicate**, [DLMF 14.29.E1](https://dlmf.nist.gov/14.29.E1):
  DLMF 14.29.1: `f` satisfies the generalized Legendre equation at `z`, `(1-z²) f'' - 2z f' +
  (ν(ν+1) - μ₁²/(2(1-z)) - μ₂²/(2(1+z))) f = 0`.
  `DLMF.Legendre.IsGeneralizedLegendreSolution` ([definition](DLMF/Legendre/Associated/BoundaryAndConnections.lean#L635)).

### §14.30 Spherical and Spheroidal Harmonics

<!-- retained entry 105 -->
- **Prolate/oblate harmonics and scaled oblate R,T**, [§14.30(i) prose](https://dlmf.nist.gov/14.30.i):
  specializations of `associatedP` and `associatedQ`; scaled functions are
  `DLMF.Legendre.scaledOblateR`, `scaledOblateT` in
  [Harmonics](DLMF/Legendre/Harmonics.lean#L938).

<!-- retained entry 103 -->
- **Spherical harmonics Yₗₘ**, [14.30.1](https://dlmf.nist.gov/14.30.E1):
  `DLMF.Legendre.sphericalHarmonicNonneg` and `sphericalHarmonic` in
  [Harmonics](DLMF/Legendre/Harmonics.lean#L48). The latter handles signed m,
  includes the DLMF phase convention, and gives zero when `|m| > l`.
  The general harmonic-polynomial objects
  `DLMF.SphericalHarmonics.IsHarmonicHomogeneous` in
  [SphericalHarmonics/Basic](DLMF/SphericalHarmonics/Basic.lean#L43)
  are related objects, not aliases for the angular functions.

<!-- retained entry 104 -->
- **Surface, tesseral and sectorial harmonics**, [14.30.2 and prose](https://dlmf.nist.gov/14.30.E2):
  `DLMF.Legendre.surfaceHarmonic` in
  [Harmonics](DLMF/Legendre/Harmonics.lean#L123), with a sine/cosine flag.
  Tesseral and sectorial are conditions on `|m|`, without separate wrappers.

## Chapter 15 — Hypergeometric function

Expanded review: all 20 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§15.1–15.20 checked; the matching section is §15.2.

### §15.2 Definitions and Analytical Properties

<!-- retained entry 106 -->
- **Gauss F = ₂F₁**, [15.2.1](https://dlmf.nist.gov/15.2.E1): Mathlib
  `ordinaryHypergeometric` and `ordinaryHypergeometricSeries` in
  [OrdinaryHypergeometric](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/OrdinaryHypergeometric.lean#L71)
  are the native series constructions. On the principal cut plane the ordinary
  continued value is expressed locally as `Gamma c * regularizedGaussHG a b c z`;
  The independent ordinary continued representative is `DLMF.Legendre.legendreGaussF` in [Hypergeometric](DLMF/Legendre/Hypergeometric.lean#L26), defined as Gamma(c) times the regularized continuation on its principal cut domain; regular lower parameters are required for that ordinary normalization.

<!-- retained entry 107 -->
- **Regularized F-bold**, [15.2.2](https://dlmf.nist.gov/15.2.E2): Mathlib
  `Complex.regularizedGaussHGFun` in
  [RegularizedHypergeometric](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean#L360)
  is the series; `DLMF.Hypergeometric.regularizedGaussHGIntegral` is Euler's
  interval integral and `regularizedGaussHG` is its parameter-shift continuation
  in [ArgumentContinuation](DLMF/Hypergeometric/Basic/PrincipalBranch.lean#L118).
  The continued function has mathematical domain `ℂ \ [1,∞)`; the integral
  construction needs `Re b > 0`, `Re(c-b) > 0`. None of these objects alone
  records both banks as a set.

<!-- retained entry 108 -->
- **Terminating exceptional-parameter interpretation**,
  [15.2.4–6](https://dlmf.nist.gov/15.2.E4): terminating sums can be expressed
  with `gaussHGCoeff` in [Basic](DLMF/Hypergeometric/Basic/GaussCoefficients.lean#L25).
  There is no named two-variable limiting object distinguishing the two
  orders of parameter limits in 15.2.5 and 15.2.6; those interpretations must
  not be inferred from a totalized series or quotient.

### §15.5 Derivatives and Contiguous Functions

- **Hypergeometric continued fractions, contiguity and Jacobi/Gegenbauer functions**, [DLMF 15.5.ii](https://dlmf.nist.gov/15.5.ii):
  The six one-step shifts are called contiguous, and integral shifts give the generalized contiguity notion of §16.3. They are parameter substitutions, without a need for six distinct global functions. The three continued fractions of §15.7 are `DLMF.Hypergeometric.gaussContinuedFraction`, `DLMF.Hypergeometric.contiguousContinuedFraction`, `DLMF.Hypergeometric.derivativeContinuedFraction` ([source](DLMF/Hypergeometric/ContinuedFractions.lean#L39)). Jacobiφλ^(α,β),Φλ^(α,β), the Jacobi transform/inverse, and the complex-degree GegenbauerCα^(λ) are defined in §15.9.11–15; `DLMF.Legendre.jacobiFunction` ([source](DLMF/Legendre/RelatedFunctions.lean#L29)), `DLMF.Legendre.gegenbauerFunction` ([source](DLMF/Legendre/RelatedFunctions.lean#L25)) give the regular-parameter Gauss-continued φ and Gegenbauer constructions. No named Φ, Jacobi transform or inverse-transform construction was identified; their weight and contour remain a gap. The polynomial counterparts in §15.9(i) are representation theorems for Chapter 18 objects.

### §15.7 Continued Fractions

- **Gauss's continued fraction, with DLMF's subtraction absorbed into the**, [DLMF 15.7.E2](https://dlmf.nist.gov/15.7.E2):
  Gauss's continued fraction, with DLMF's subtraction absorbed into the
  partial numerators. Mathlib's stream index `k` corresponds to DLMF's `k+1`.
  `DLMF.Hypergeometric.gaussContinuedFraction` ([definition](DLMF/Hypergeometric/ContinuedFractions.lean#L39)).

- **Second expansion of the same quotient**, [DLMF 15.7.E4](https://dlmf.nist.gov/15.7.E4):
  The second expansion of the same quotient.
  `DLMF.Hypergeometric.contiguousContinuedFraction` ([definition](DLMF/Hypergeometric/ContinuedFractions.lean#L49)).

- **Continued fraction associated with the derivative quotient**, [DLMF 15.7.E6](https://dlmf.nist.gov/15.7.E6):
  The continued fraction associated with the derivative quotient.
  `DLMF.Hypergeometric.derivativeContinuedFraction` ([definition](DLMF/Hypergeometric/ContinuedFractions.lean#L57)).

### §15.10 Hypergeometric Differential Equation

- **Gauss equation, local/logarithmic solutions and Kummer solutions**, [DLMF 15.10](https://dlmf.nist.gov/15.10):
  `DLMF.Hypergeometric.gaussOperator`, `DLMF.Hypergeometric.zeroSecond`, `DLMF.Hypergeometric.oneFirst`, `DLMF.Hypergeometric.oneSecond`, `DLMF.Hypergeometric.infinityFirst`, `DLMF.Hypergeometric.solutionWronskian`, and the three logarithmic second-solution constructions are in [Solutions/Equation](DLMF/Hypergeometric/Solutions/Equation.lean#L41). The infinity solutions with the appropriate bank phases are `DLMF.Hypergeometric.kummerFive`, `DLMF.Hypergeometric.kummerSix`, `DLMF.Hypergeometric.kummerFiveLeft`, `DLMF.Hypergeometric.kummerSixLeft` ([source](DLMF/Hypergeometric/Kummer.lean#L32)). Kummer's24 solutions are transformations of these local expressions, not 24 independently chosen analytic continuations on one global domain.

  [DLMF 15.10.E1](https://dlmf.nist.gov/15.10.E1):
  The Gauss differential operator, without division at its singular points.
  `DLMF.Hypergeometric.gaussOperator` ([definition](DLMF/Hypergeometric/Solutions/Equation.lean#L41)).

  [DLMF 15.10.E2](https://dlmf.nist.gov/15.10.E2):
  The second solution at zero. The first is Mathlib's `ordinaryHypergeometric`.
  `DLMF.Hypergeometric.zeroSecond` ([definition](DLMF/Hypergeometric/Solutions/Equation.lean#L50)).

  [DLMF 15.10.E4](https://dlmf.nist.gov/15.10.E4):
  The first standard Gauss hypergeometric solution about one, given by the series in `1-z` with
  denominator parameter `a+b-c+1`.
  `DLMF.Hypergeometric.oneFirst` ([definition](DLMF/Hypergeometric/Solutions/Equation.lean#L54)).

  [DLMF 15.10.E4](https://dlmf.nist.gov/15.10.E4):
  The second standard Gauss solution about one, with principal power `(1-z)^(c-a-b)` multiplying
  the transformed series.
  `DLMF.Hypergeometric.oneSecond` ([definition](DLMF/Hypergeometric/Solutions/Equation.lean#L59)).

  [DLMF 15.10.E6](https://dlmf.nist.gov/15.10.E6):
  Interchanging `a,b` gives the second solution at infinity.
  `DLMF.Hypergeometric.infinityFirst` ([definition](DLMF/Hypergeometric/Solutions/Equation.lean#L65)).

  [DLMF 15.10.E15](https://dlmf.nist.gov/15.10.E15):
  Kummer's fifth solution on the local chart at infinity.
  `DLMF.Hypergeometric.kummerFive` ([definition](DLMF/Hypergeometric/Kummer.lean#L32)).

  [DLMF 15.10.E15](https://dlmf.nist.gov/15.10.E15):
  A second chart for Kummer's fifth solution, overlapping the disk at zero.
  `DLMF.Hypergeometric.kummerFiveLeft` ([definition](DLMF/Hypergeometric/Kummer.lean#L40)).

  [DLMF 15.10.E16](https://dlmf.nist.gov/15.10.E16):
  Kummer's sixth solution on the local chart at infinity.
  `DLMF.Hypergeometric.kummerSix` ([definition](DLMF/Hypergeometric/Kummer.lean#L36)).

  [DLMF 15.10.E16](https://dlmf.nist.gov/15.10.E16):
  A second chart for Kummer's sixth solution.
  `DLMF.Hypergeometric.kummerSixLeft` ([definition](DLMF/Hypergeometric/Kummer.lean#L45)).

- **Logarithmic second solution for a positive integral denominator (generic numerators)**, [DLMF 15.10.E8](https://dlmf.nist.gov/15.10.E8):
  The logarithmic second solution for a positive integral denominator (generic numerators).
  `DLMF.Hypergeometric.logarithmicSecond` ([definition](DLMF/Hypergeometric/Solutions/Equation.lean#L520)).

- **Logarithmic second solution with one terminating numerator**, [DLMF 15.10.E9](https://dlmf.nist.gov/15.10.E9):
  The logarithmic second solution with one terminating numerator.
  `DLMF.Hypergeometric.logarithmicSecondTerminating` ([definition](DLMF/Hypergeometric/Solutions/Equation.lean#L530)).

- **Logarithmic second solution with two terminating numerators**, [DLMF 15.10.E10](https://dlmf.nist.gov/15.10.E10):
  The logarithmic second solution with two terminating numerators.
  `DLMF.Hypergeometric.logarithmicSecondBothTerminating` ([definition](DLMF/Hypergeometric/Solutions/Equation.lean#L543)).

### §15.11 Riemann’s Differential Equation

- **Riemann equation and P-symbol**, [DLMF 15.11](https://dlmf.nist.gov/15.11):
  `DLMF.Hypergeometric.riemannOperator`, `DLMF.Hypergeometric.riemannNormalOperator`, and `DLMF.Hypergeometric.riemannSolutions` ([source](DLMF/Hypergeometric/Riemann.lean#L31)) implement the three-singularity equation and its solution set. The P-symbol is a set of sufficiently differentiable solutions on an explicit domain, rather than a distinguished scalar function. The exponent-sum/Fuchs relation and Möbius change of variable remain hypotheses/formulas in the transformations; singularities at∞are limiting normal forms.

  [DLMF 15.11.E1](https://dlmf.nist.gov/15.11.E1):
  Riemann's differential operator with three finite singular points.
  `DLMF.Hypergeometric.riemannOperator` ([definition](DLMF/Hypergeometric/Riemann.lean#L31)).

  [DLMF 15.11.E3](https://dlmf.nist.gov/15.11.E3):
  The P-symbol denotes a set of solutions, not a distinguished scalar function.
  The domain is explicit; differentiability is required there.
  `DLMF.Hypergeometric.riemannSolutions` ([definition](DLMF/Hypergeometric/Riemann.lean#L39)).

### §15.12 Asymptotic Approximations

- **Hypergeometric generating coefficients and zero count**, [DLMF 15.12.E4](https://dlmf.nist.gov/15.12.E4):
  qₛ coefficients are `DLMF.Hypergeometric.largeDenominatorGenerating`, `DLMF.Hypergeometric.largeDenominatorCoeff`, with removable `DLMF.Hypergeometric.expSubOneDiv` ([source](DLMF/Hypergeometric/Asymptotics.lean#L137)). The pₛ,qₛ product coefficients of 15.16.2 and implicit asymptotic variables of 15.12 are additional formula-defined objects; no independently named local pₛ/qₛ or general coordinate construction was found. The N(a,b,c) of §15.13 denotes the number of zeros in the stated sector, with exceptional polynomial/undefined cases excluded; it is not an unconstrained integer parameter.

  [DLMF 15.12.E4](https://dlmf.nist.gov/15.12.E4):
  Generating function for the large-denominator coefficients.
  `DLMF.Hypergeometric.largeDenominatorGenerating` ([definition](DLMF/Hypergeometric/Asymptotics.lean#L140)).

  [DLMF 15.12.E4](https://dlmf.nist.gov/15.12.E4):
  Taylor coefficients of DLMF's generating function.
  `DLMF.Hypergeometric.largeDenominatorCoeff` ([definition](DLMF/Hypergeometric/Asymptotics.lean#L145)).

## Chapter 16 — Generalized hypergeometric functions and Meijer G

Expanded review: all 27 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§16.1–16.27 checked; matching headings are §16.2 and §16.17.

### §16.2 Definition and Analytic Properties

<!-- retained entry 109 -->
- **Generalized ₚFq and its formal/terminating series**, [16.2.1](https://dlmf.nist.gov/16.2.E1):
  `DLMF.Hypergeometric.genCoeff`, `genFormalSeries`, `genFiniteHG`, `genHG`
  in [GeneralizedHypergeometric/Basic](DLMF/GeneralizedHypergeometric/Basic/ParametersAndSeries.lean#L33).
  `GenPrincipalContinuation` specifies the principal continuation for `p=q+1`;
  `genHGLower` separately gives lower-bank values. For `p>q+1` nonterminating
  series values are not a continuation: use the Barnes constructions
  `genHasBarnesValueLog`, `genBarnesHGLog` in the same file.

<!-- retained entry 110 -->
- **Excess γq**, [16.2.2](https://dlmf.nist.gov/16.2.E2):
  `DLMF.Hypergeometric.genExcess` in
  [Basic](DLMF/GeneralizedHypergeometric/Basic/ParametersAndSeries.lean#L59).

- **Generalized hypergeometric excess and classifications**, [DLMF 16.2.E2](https://dlmf.nist.gov/16.2.E2):
  The excessγ_q is `DLMF.Hypergeometric.genExcess`; regularized and ordinary/finite series are distinct constructions. Well-poised, very-well-poised andk-balanced classifications are `DLMF.Hypergeometric.genWellPoised`, the corresponding half-parameter condition, and `DLMF.Hypergeometric.genKBalanced` ([source](DLMF/GeneralizedHypergeometric/UnitArgument.lean#L38)). Balanced/Saalschützian means1-balanced with termination as specified. The bilateral coefficient and series are `DLMF.Hypergeometric.genBilateralCoeff`, `DLMF.Hypergeometric.genBilateralHG` ([source](DLMF/GeneralizedHypergeometric/Basic/BilateralAndBarnes.lean#L26)); negative indices use the appropriate generalized factorial convention.

<!-- retained entry 111 -->
- **Regularized generalized hypergeometric function**, [16.2.5](https://dlmf.nist.gov/16.2.E5):
  Mathlib `Complex.regularizedHGFunCoeff`, `regularizedHGFunSeries`,
  `regularizedHGFun` in
  [RegularizedHypergeometric](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean#L67)
  are native series objects. `DLMF.Hypergeometric.genRegularizedHG` in
  [Basic](DLMF/GeneralizedHypergeometric/Basic/PrincipalContinuation.lean#L36) additionally chooses
  the specified principal continuation when `p=q+1`; existence obligations
  are separate. Multisets encode unordered upper and lower parameter lists.

### §16.4 Argument Unity

- **Well-poised parameter vectors, in exactly the indexing order of 16.4.1**, [DLMF 16.4.E1](https://dlmf.nist.gov/16.4.E1):
  Well-poised parameter vectors, in exactly the indexing order of 16.4.1.
  `DLMF.Hypergeometric.genWellPoised` ([definition](DLMF/GeneralizedHypergeometric/UnitArgument.lean#L38)).

- **K-balanced terminating unity series (16.4.2); balanced means k=1**, [DLMF 16.4.E2](https://dlmf.nist.gov/16.4.E2):
  A k-balanced terminating unity series (16.4.2); balanced means k=1.
  `DLMF.Hypergeometric.genKBalanced` ([definition](DLMF/GeneralizedHypergeometric/UnitArgument.lean#L47)).

- **Thomae expression supplies parameter continuation beyond the original unit**, [DLMF 16.4.E11](https://dlmf.nist.gov/16.4.E11):
  The Thomae expression supplies parameter continuation beyond the original unit
  series region; at Gamma poles its totalized value is not an assigned finite limit.
  `DLMF.Hypergeometric.gen3F2UnitThomae` ([definition](DLMF/GeneralizedHypergeometric/UnitArgument.lean#L761)).

- **Formal bilateral hypergeometric coefficients and series**, [DLMF 16.4.E16](https://dlmf.nist.gov/16.4.E16):
  Formal bilateral hypergeometric coefficient, with no factorial factor (16.4.16).
  `DLMF.Hypergeometric.genBilateralCoeff` ([definition](DLMF/GeneralizedHypergeometric/Basic/BilateralAndBarnes.lean#L26)).

  [DLMF 16.4.E16](https://dlmf.nist.gov/16.4.E16):
  Totalized bilateral series. Outside an explicitly proved convergence regime this is
  only a formal-series interface, not an analytically continued function (16.4.16).
  `DLMF.Hypergeometric.genBilateralHG` ([definition](DLMF/GeneralizedHypergeometric/Basic/BilateralAndBarnes.lean#L31)).

### §16.8 Differential Equations

- **Ordinary/regular singularities and generalized hypergeometric ODE**, [DLMF 16.8](https://dlmf.nist.gov/16.8):
  The classification extends §2.7 to arbitrary order; the local predicates are `Complex.linearODEOrdinaryAt`, `Complex.linearODEAtMostRegularAt`, `Complex.linearODERegularSingularAt`, `Complex.linearODEIrregularAt` and their infinity counterparts ([source](DLMFMathlib/Analysis/ODE/Singularities.lean#L32)). The module path is `DLMFMathlib.Analysis.ODE.Singularities`; the declaration namespace is `Complex`. Eulerθ=zD is `DLMF.Hypergeometric.eulerTheta`, while the normalized differential form, coefficient polynomials and Frobenius solutions are `DLMF.Hypergeometric.genNormalizedODE`, `DLMF.Hypergeometric.genD`, `DLMF.Hypergeometric.genThetaA`, `DLMF.Hypergeometric.genThetaB`, `DLMF.Hypergeometric.genThetaDCoeff`, `DLMF.Hypergeometric.genODEAlpha`, `DLMF.Hypergeometric.genODEBeta`, `DLMF.Hypergeometric.genODEOrder`, `DLMF.Hypergeometric.genODECoeff`, `DLMF.Hypergeometric.genODESolution`, `DLMF.Hypergeometric.genFundamentalSystem`, `DLMF.Hypergeometric.genFrobeniusRoot`, `DLMF.Hypergeometric.genFrobeniusZero`, `DLMF.Hypergeometric.genHGNegativeLog`, `DLMF.Hypergeometric.genFrobeniusInfinityLog`, `DLMF.Hypergeometric.genInfinityConnectionCoeff`, `DLMF.Hypergeometric.genCenteredInfinityTerm` ([source](DLMF/GeneralizedHypergeometric/DifferentialEquations.lean#L32)). Ordinary powers and full logarithmic sheets remain separate.

  [DLMF 16.8.E1](https://dlmf.nist.gov/16.8.E1):
  Normalized scalar ODE value (16.8.1).
  `DLMF.Hypergeometric.genNormalizedODE` ([definition](DLMF/GeneralizedHypergeometric/DifferentialEquations.lean#L32)).

  [DLMF 16.8.E2](https://dlmf.nist.gov/16.8.E2):
  The Euler operator `θ f = z f'`.
  `DLMF.Hypergeometric.eulerTheta` ([definition](DLMF/Hypergeometric/Generalized.lean#L39)).

  [DLMF 16.8.E2](https://dlmf.nist.gov/16.8.E2):
  Differentiation operator; theta itself is the existing `eulerTheta` (16.8.2).
  `DLMF.Hypergeometric.genD` ([definition](DLMF/GeneralizedHypergeometric/DifferentialEquations.lean#L37)).

  [DLMF 16.8.E6](https://dlmf.nist.gov/16.8.E6):
  The nonresonant Frobenius solutions at zero (16.8.6).
  `DLMF.Hypergeometric.genFrobeniusZero` ([definition](DLMF/GeneralizedHypergeometric/DifferentialEquations.lean#L86)).

  [DLMF 16.8.E7](https://dlmf.nist.gov/16.8.E7):
  The nonresonant infinity solutions with an explicit log(-z) sheet (16.8.7).
  `DLMF.Hypergeometric.genFrobeniusInfinityLog` ([definition](DLMF/GeneralizedHypergeometric/DifferentialEquations.lean#L102)).

### §16.11 Asymptotic Expansions

- **Formal exponential/algebraic hypergeometric expansions**, [DLMF 16.11](https://dlmf.nist.gov/16.11):
  κ,ν,augmented lower parameters,e_{k,m},cₖ are `DLMF.Hypergeometric.genAsymptoticKappa`, `DLMF.Hypergeometric.genAsymptoticNu`, `DLMF.Hypergeometric.genAsymptoticAugment`, `DLMF.Hypergeometric.genAsymptoticEkm`, `DLMF.Hypergeometric.genAsymptoticCRaw`. Repeated-parameter continuation uses `DLMF.Hypergeometric.genAsymptoticPerturb`, `DLMF.Hypergeometric.genAsymptoticC`; its identifying limit theorem is still admitted. E,H are represented by `DLMF.Hypergeometric.genETermLog`, `DLMF.Hypergeometric.genHTermLog`; repeated upper poles use `DLMF.Hypergeometric.genHPoleSet`, `DLMF.Hypergeometric.genHResidueLog`, `DLMF.Hypergeometric.genHPoleTrunc`, `DLMF.Hypergeometric.genHTruncLog`, retaining logarithmic residue terms ([source](DLMF/GeneralizedHypergeometric/Asymptotics.lean#L34)). Remainder scales and shifted parameters also have actual constructions there. These formal/asymptotic series must not be described as convergent whole-plane definitions.

  [DLMF 16.11.E1](https://dlmf.nist.gov/16.11.E1):
  The kth formal exponential term E_(p,q) on the logarithm sheet w (16.11.1).
  `DLMF.Hypergeometric.genETermLog` ([definition](DLMF/GeneralizedHypergeometric/Asymptotics.lean#L73)).

  [DLMF 16.11.E2](https://dlmf.nist.gov/16.11.E2):
  The formal algebraic simple-pole term H_(p,q) on logarithm sheet w (16.11.2).
  `DLMF.Hypergeometric.genHTermLog` ([definition](DLMF/GeneralizedHypergeometric/Asymptotics.lean#L82)).

  [DLMF 16.11.E3](https://dlmf.nist.gov/16.11.E3):
  The positive exponential index kappa, for p<q+1 (16.11.3).
  `DLMF.Hypergeometric.genAsymptoticKappa` ([definition](DLMF/GeneralizedHypergeometric/Asymptotics.lean#L34)).

  [DLMF 16.11.E3](https://dlmf.nist.gov/16.11.E3):
  The full complex exponent nu (16.11.3).
  `DLMF.Hypergeometric.genAsymptoticNu` ([definition](DLMF/GeneralizedHypergeometric/Asymptotics.lean#L38)).

  [DLMF 16.11.E4](https://dlmf.nist.gov/16.11.E4):
  Raw c coefficients from the complete finite recurrence (16.11.4).
  `DLMF.Hypergeometric.genAsymptoticCRaw` ([definition](DLMF/GeneralizedHypergeometric/Asymptotics.lean#L56)).

  [DLMF 16.11.E5](https://dlmf.nist.gov/16.11.E5):
  The raw e_(k,m) coefficient, where the augmented lower parameters are distinct.
  `DLMF.Hypergeometric.genAsymptoticEkm` ([definition](DLMF/GeneralizedHypergeometric/Asymptotics.lean#L47)).

### §16.13 Appell Functions

<!-- retained entry extra111 -->
**Appell F₁,F₂,F₃,F₄** definitions occur under
[§16.13 “Appell Functions”, 16.13.1–4](https://dlmf.nist.gov/16.13):
`DLMF.Hypergeometric.appF1`, `appF2`, `appF3` in
[DefinitionsAndSeries](DLMF/GeneralizedHypergeometric/Appell/Basic/Series.lean#L77),
and `appF4` in [AppellF4](DLMF/Hypergeometric/Basic/AppellF4.lean#L41).
The four `appF1Euler`–`appF4Euler` definitions in
[EulerIntegrals](DLMF/GeneralizedHypergeometric/Appell/Basic/EulerBranches.lean#L52)
are independent integral constructions; their domains differ from the double-series
domains. `appF4InfinityExpression`, `appF4InfinityBranch` in
[AppellContinuation](DLMF/GeneralizedHypergeometric/AppellContinuation.lean#L24)
give a particular continued branch. `IsAppellContinuation`, `IsAppellBranchAt`
specify general continuation data, rather than a globally single-valued Appell function.

- **Appell series, Horn examples and independent Euler integrals**, [DLMF 16.13](https://dlmf.nist.gov/16.13):
  F₁,F₂,F₃ have explicit coefficient and double-series constructions `DLMF.Hypergeometric.appF1Coeff`, `DLMF.Hypergeometric.appF2Coeff`, `DLMF.Hypergeometric.appF3Coeff`, `DLMF.Hypergeometric.appF1`, `DLMF.Hypergeometric.appF2`, `DLMF.Hypergeometric.appF3` ([source](DLMF/GeneralizedHypergeometric/Appell/Basic/Series.lean#L62)); F₄ is `DLMF.Hypergeometric.appF4` ([source](DLMF/Hypergeometric/Basic/AppellF4.lean#L41)). HornG₂,G₃ of 16.14.5–6 are `DLMF.Hypergeometric.hornG2`, `DLMF.Hypergeometric.hornG3` ([source](DLMF/GeneralizedHypergeometric/Appell/Basic/Series.lean#L95)), with the stated sufficient convergence regions. Independent `DLMF.Hypergeometric.appF1Euler`, `DLMF.Hypergeometric.appF2Euler`, `DLMF.Hypergeometric.appF3Euler`, `DLMF.Hypergeometric.appF4Euler` ([source](DLMF/GeneralizedHypergeometric/Appell/Basic/EulerBranches.lean#L52)) implement the integral formulas of §16.15; F₃ uses the triangleu,v≥0,u+v≤1, and F₄'s variables arex(1−y),y(1−x). Representation/continuation statements are separate from these actual integral constructions.

  [DLMF 16.13.E1](https://dlmf.nist.gov/16.13.E1):
  Appell F1 double-series coefficient.
  `DLMF.Hypergeometric.appF1Coeff` ([definition](DLMF/GeneralizedHypergeometric/Appell/Basic/Series.lean#L62)).

  [DLMF 16.13.E2](https://dlmf.nist.gov/16.13.E2):
  Appell F2 double-series coefficient.
  `DLMF.Hypergeometric.appF2Coeff` ([definition](DLMF/GeneralizedHypergeometric/Appell/Basic/Series.lean#L67)).

  [DLMF 16.13.E3](https://dlmf.nist.gov/16.13.E3):
  Appell F3 double-series coefficient.
  `DLMF.Hypergeometric.appF3Coeff` ([definition](DLMF/GeneralizedHypergeometric/Appell/Basic/Series.lean#L72)).

### §16.14 Partial Differential Equations

- **Horn G2 in the gamma-ratio normalization**, [DLMF 16.14.E5](https://dlmf.nist.gov/16.14.E5):
  Horn G2 in the gamma-ratio normalization.
  `DLMF.Hypergeometric.hornG2` ([definition](DLMF/GeneralizedHypergeometric/Appell/Basic/Series.lean#L95)).

- **Horn G3 in the gamma-ratio normalization**, [DLMF 16.14.E6](https://dlmf.nist.gov/16.14.E6):
  Horn G3 in the gamma-ratio normalization.
  `DLMF.Hypergeometric.hornG3` ([definition](DLMF/GeneralizedHypergeometric/Appell/Basic/Series.lean#L101)).

### §16.15 Integral Representations and Integrals

- **Euler square-integral branch of F2**, [DLMF 16.15.E2](https://dlmf.nist.gov/16.15.E2):
  The Euler square-integral branch of F2.
  `DLMF.Hypergeometric.appF2Euler` ([definition](DLMF/GeneralizedHypergeometric/Appell/Basic/EulerBranches.lean#L57)).

- **Euler simplex-integral branch of F3**, [DLMF 16.15.E3](https://dlmf.nist.gov/16.15.E3):
  The Euler simplex-integral branch of F3.
  `DLMF.Hypergeometric.appF3Euler` ([definition](DLMF/GeneralizedHypergeometric/Appell/Basic/EulerBranches.lean#L63)).

### §16.17 Definition

- **Meijer G residues and logarithmic ODE solutions**, [DLMF 16.17](https://dlmf.nist.gov/16.17):
  The contour-dependent G construction also has its kernel `DLMF.Hypergeometric.meijerGKernelLog`, allowed contour region and `DLMF.Hypergeometric.MeijerGHasValueLog`, selected `DLMF.Hypergeometric.meijerGLog` ([source](DLMF/GeneralizedHypergeometric/MeijerG.lean#L50)). The residue coefficients in 16.17.3 are `DLMF.Hypergeometric.meijerResidueCoeff`; `DLMF.Hypergeometric.MeijerLogEquation`, `DLMF.Hypergeometric.meijerFundamentalTerm` represent §16.21 ([source](DLMF/GeneralizedHypergeometric/MeijerGRelations.lean#L47)). Their path/separation hypotheses and logarithmic coordinate carry genuine data; a value chosen via totalized contour integrals does not prove independence of the contour. Application-only functions of §§16.23–24 are named references or specializations of already listed hypergeometric functions.

  [DLMF 16.17.E3](https://dlmf.nist.gov/16.17.E3):
  The source A_{p,q,k}^{m,n}, with indices starting at zero. It is used only for k<m≤q.
  `DLMF.Hypergeometric.meijerResidueCoeff` ([definition](DLMF/GeneralizedHypergeometric/MeijerGRelations.lean#L47)).

<!-- retained entry 112 -->
- **Meijer G, logarithmic branches, and the three admissible contour types**,
  [16.17.1 and contour prose](https://dlmf.nist.gov/16.17.E1):
  `DLMF.Hypergeometric.MeijerGParameters`, `MeijerContourKind`,
  `MeijerGContour`, `meijerGKernelLog`, `MeijerGHasValueLog`,
  `MeijerGConvergesLog`, `meijerGLog`, and `meijerG` in
  [MeijerG](DLMF/GeneralizedHypergeometric/MeijerG.lean#L27).
  Pole separation, orientation and convergence are recorded explicitly by
  `Valid`, `Admissible`, and `meijerGContourRegion`. The principal function
  specializes the logarithmic one with `Complex.log`; a zero fallback outside
  the existence predicate is not a convergent contour value.

### §16.21 Differential Equation

- **Meijer differential equation on the logarithmic plane; d/dw is z*d/dz**, [DLMF 16.21.E1](https://dlmf.nist.gov/16.21.E1):
  The Meijer differential equation on the logarithmic plane; d/dw is z*d/dz.
  `DLMF.Hypergeometric.MeijerLogEquation` ([definition](DLMF/GeneralizedHypergeometric/MeijerGRelations.lean#L240)).

- **Jth displayed G-solution, with the jth bottom parameter moved to the first position**, [DLMF 16.21.E2](https://dlmf.nist.gov/16.21.E2):
  The jth displayed G-solution, with the jth bottom parameter moved to the first position.
  `DLMF.Hypergeometric.meijerFundamentalTerm` ([definition](DLMF/GeneralizedHypergeometric/MeijerGRelations.lean#L266)).

## Chapter 17 — q-hypergeometric and related functions

Expanded review: all 19 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§17.1–17.19 checked; no heading contains “Definition” or
“Definitions”. The following are complementary entries from
§17.2 “Calculus” and §17.4 “Basic Hypergeometric Functions”.

### §17.1 Special Notation

- **q-notation, q-numbers and Jackson calculus**, [DLMF 17.1](https://dlmf.nist.gov/17.1):
  Besides q-Pochhammer products and q-binomial coefficients, `DLMF.QHypergeometric.qIdem` ([source](DLMF/QHypergeometric/Basic/Series.lean#L96)) sums the terms with another singled-out parameter; idem excludes the original term, so f+idem gives the full parameter-swap sum. D_q and its iterates, the Jackson integrals on [0,a],[a,b], and the bilateral infinite-range integral are actual q-calculus objects, including `DLMF.QHypergeometric.qDerivExtended`, `DLMF.QSeries.jacksonIntegral`, `DLMF.QHypergeometric.jacksonBilateral` ([source](DLMF/QHypergeometric/Calculus.lean#L37), [source](DLMF/QSeries/Basic/Pochhammer.lean#L34)). The integral retains its geometric lattice and convergence conditions; it is not ordinary Lebesgue integration with a renamed variable.

### §17.2 Calculus

<!-- retained entry 113 -->
- **Finite, negative-integral, complex-order and infinite q-Pochhammer
  symbols**, [17.2.1–6](https://dlmf.nist.gov/17.2.E1):
  `DLMF.QSeries.qPochhammer`, `qPochhammerInf` in
  [Pochhammer](DLMF/QSeries/Basic/Pochhammer.lean#L23);
  list variants `DLMF.QHypergeometric.qPochhammerList`,
  `qPochhammerListInt`, `qPochhammerListInf`, and complex-order
  `qPochhammerOrder` in [Basic](DLMF/QHypergeometric/Basic/Series.lean#L23).
  Infinite products and complex powers require their convergence and branch
  hypotheses; a product quotient is not automatically valid at zeros.

<!-- retained entry 114 -->
- **q-binomial coefficients**, [17.2.27](https://dlmf.nist.gov/17.2.E27):
  recurrence definition `DLMF.QSeries.qBinom` in
  [QBinomial](DLMF/QSeries/Basic/Calculus.lean#L21) and integer-top extension
  `DLMF.QHypergeometric.qBinomialInt` in
  [Calculus](DLMF/QHypergeometric/Calculus.lean#L70).

<!-- retained entry 115 -->
- **q-derivative and iterated q-derivative**, [17.2.41–42](https://dlmf.nist.gov/17.2.E41):
  `DLMF.QSeries.qDeriv` in [QCalculus](DLMF/QSeries/Basic/Calculus.lean#L27)
  is the raw quotient; `DLMF.QHypergeometric.qDerivExtended` and
  `qDerivIterate` in [Calculus](DLMF/QHypergeometric/Calculus.lean#L37)
  additionally supply the ordinary derivative at zero.

<!-- retained entry 116 -->
- **Jackson q-integrals**, [17.2.45–48](https://dlmf.nist.gov/17.2.E45):
  `DLMF.QSeries.jacksonIntegral` in [Pochhammer](DLMF/QSeries/Basic/Pochhammer.lean#L34),
  and `DLMF.QHypergeometric.jacksonBetween`, `jacksonBilateral`,
  `HasNaturalJacksonIntegral`, `HasNaturalJacksonBilateral` in
  [Calculus](DLMF/QHypergeometric/Calculus.lean#L44).
  The predicates retain convergence information separately from totalized sums.

### §17.3 q -Elementary and q -Special Functions

- **q-elementary and Carlitz coefficient families**, [DLMF 17.3](https://dlmf.nist.gov/17.3):
  `DLMF.QHypergeometric.qExp`, `DLMF.QHypergeometric.qExpBig`, `DLMF.QHypergeometric.qSin`, `DLMF.QHypergeometric.qSinBig`, `DLMF.QHypergeometric.qCos`, `DLMF.QHypergeometric.qCosBig`, `DLMF.QHypergeometric.qBernoulli`, plus the untagged `DLMF.QHypergeometric.qEulerian`, `DLMF.QHypergeometric.qStirlingSecond` ([source](DLMF/QHypergeometric/Elementary.lean#L29)) implement all the displayed families. The exponentials include (1−q) scaling and independent product constructions; the little version is meromorphic, the big version entire for |q|<1. Carlitzβₙ is generally rational inq, while the other two displayed families are polynomials on their intended indices; the recurrence-based q-Stirling definition includes removable endpoint conventions.

  [DLMF 17.3.E1](https://dlmf.nist.gov/17.3.E1):
  The scaled little q-exponential, including its meromorphic product continuation.
  `DLMF.QHypergeometric.qExp` ([definition](DLMF/QHypergeometric/Elementary.lean#L29)).

  [DLMF 17.3.E2](https://dlmf.nist.gov/17.3.E2):
  The scaled big q-exponential, an entire product in its argument when |q|<1.
  `DLMF.QHypergeometric.qExpBig` ([definition](DLMF/QHypergeometric/Elementary.lean#L32)).

  [DLMF 17.3.E3](https://dlmf.nist.gov/17.3.E3):
  The little q-sine.
  `DLMF.QHypergeometric.qSin` ([definition](DLMF/QHypergeometric/Elementary.lean#L35)).

  [DLMF 17.3.E4](https://dlmf.nist.gov/17.3.E4):
  The big q-sine.
  `DLMF.QHypergeometric.qSinBig` ([definition](DLMF/QHypergeometric/Elementary.lean#L38)).

  [DLMF 17.3.E5](https://dlmf.nist.gov/17.3.E5):
  The little q-cosine.
  `DLMF.QHypergeometric.qCos` ([definition](DLMF/QHypergeometric/Elementary.lean#L41)).

  [DLMF 17.3.E6](https://dlmf.nist.gov/17.3.E6):
  The big q-cosine.
  `DLMF.QHypergeometric.qCosBig` ([definition](DLMF/QHypergeometric/Elementary.lean#L44)).

  [DLMF 17.3.E7](https://dlmf.nist.gov/17.3.E7):
  Carlitz's q-Bernoulli expression, with the principal power q^(rx).
  `DLMF.QHypergeometric.qBernoulli` ([definition](DLMF/QHypergeometric/Elementary.lean#L47)).

### §17.4 Basic Hypergeometric Functions

- **Basic hypergeometric continuations and poised classifications**, [DLMF 17.4](https://dlmf.nist.gov/17.4):
  The unilateral/bilateral series `DLMF.QHypergeometric.qPhi`, `DLMF.QHypergeometric.qPsi`, their finite forms/coefficient functions and `DLMF.QHypergeometric.qAppell1`, `DLMF.QHypergeometric.qAppell2`, `DLMF.QHypergeometric.qAppell3`, `DLMF.QHypergeometric.qAppell4` constructions retain the Gasper–Rahman phase factor convention; older Bailey/Slater notation differs. The five class predicates are `DLMF.QHypergeometric.qBalanced`, `DLMF.QHypergeometric.qKBalanced`, `DLMF.QHypergeometric.qWellPoised`, `DLMF.QHypergeometric.qVeryWellPoised`, `DLMF.QHypergeometric.qNearlyPoised` ([source](DLMF/QHypergeometric/Basic/Series.lean#L42)). `DLMF.QHypergeometric.qOnePhiZeroContinuation` ([source](DLMF/QHypergeometric/BasicSummations.lean#L31)), `DLMF.QHypergeometric.qHeineJacksonValue` ([source](DLMF/QHypergeometric/BasicSummations.lean#L33)), `DLMF.QHypergeometric.qHeineBarnesKernel` ([source](DLMF/QHypergeometric/BasicSummations.lean#L37)), `DLMF.QHypergeometric.qHeineBarnesLeft` ([source](DLMF/QHypergeometric/BasicSummations.lean#L41)), `DLMF.QHypergeometric.qHeineBarnesRight` ([source](DLMF/QHypergeometric/BasicSummations.lean#L44)) provide a product continuation and independent Jackson/Barnes expressions. Common-zero removal is an existential analytic-germ theorem, without another selected function. No separately named global two-phi-one continued function was found. Bibasic identities use two bases; they do not define a new q-Gamma branch.

<!-- retained entry 117 -->
- **Basic unilateral and bilateral hypergeometric series**,
  [17.4.1](https://dlmf.nist.gov/17.4.E1), [17.4.3](https://dlmf.nist.gov/17.4.E3):
  `DLMF.QHypergeometric.qPhi`, `qPsi`, with terms and finite partial sums in
  [Basic](DLMF/QHypergeometric/Basic/Series.lean#L42). The exponent includes DLMF's
  `(-1)ⁿ q^(n(n-1)/2)` factor; convergence regions and exceptional q-powers
  remain hypotheses, not alternative continuation definitions.

<!-- retained entry 118 -->
- **Four q-Appell functions**, [17.4.5–8](https://dlmf.nist.gov/17.4.E5):
  `DLMF.QHypergeometric.qAppell1`, `qAppell2`, `qAppell3`, `qAppell4`
  in [Appell](DLMF/QHypergeometric/Appell.lean#L29), double series with
  their parameter order matching the displayed formulas.

<!-- retained entry 119 -->
- **Balanced/Saalschützian, k-balanced, well-poised, very-well-poised and
  nearly-poised series**, [17.4.9–13](https://dlmf.nist.gov/17.4.E9):
  `DLMF.QHypergeometric.qBalanced`, `qKBalanced`, `qWellPoised`,
  `qVeryWellPoised`, `qNearlyPoised` in
  [Basic](DLMF/QHypergeometric/Basic/Series.lean#L75).

### §17.12 Bailey Pairs

- **Bailey transforms, pairs and chains**, [DLMF 17.12](https://dlmf.nist.gov/17.12):
  `DLMF.Bailey.IsBaileyPair` ([source](DLMF/Bailey.lean#L213)) is the finite transform relation for each index. The general transform sequences are `DLMF.QHypergeometric.generalBaileyBeta`, `DLMF.QHypergeometric.generalBaileyGamma`; `DLMF.QHypergeometric.IsBaileyChain`, the actual iterated transform/pair constructions and `DLMF.QHypergeometric.rogersBaileyAlpha`, `DLMF.QHypergeometric.rogersBaileyBeta` are in [BaileyPairs](DLMF/QHypergeometric/BaileyPairs.lean#L25). An existential/invariant chain predicate differs from a chosen sequence. G(q),H(q) in §17.14 denote the Rogers–Ramanujan sums already appearing in §17.2, with any existing named sum/product variants recorded at their first entry. Constant-term identities use the existing coefficient operation on the relevant Laurent expressions.

  [DLMF 17.12.E2](https://dlmf.nist.gov/17.12.E2):
  The finite row of a general Bailey transform.
  `DLMF.QHypergeometric.generalBaileyBeta` ([definition](DLMF/QHypergeometric/BaileyPairs.lean#L25)).

  [DLMF 17.12.E2](https://dlmf.nist.gov/17.12.E2):
  The infinite column of a general Bailey transform.
  `DLMF.QHypergeometric.generalBaileyGamma` ([definition](DLMF/QHypergeometric/BaileyPairs.lean#L30)).

  [DLMF 17.12.E3](https://dlmf.nist.gov/17.12.E3):
  A Bailey pair relative to `a`: `β_n = ∑_{k=0}^n α_k / ((q;q)_{n-k} (aq;q)_{n+k})`.
  `DLMF.Bailey.IsBaileyPair` ([definition](DLMF/Bailey.lean#L213)).

  [DLMF 17.12](https://dlmf.nist.gov/17.12#Px4.p2):
  DLMF 17.12: an infinite chain is obtained by successive applications of 17.12.5.
  The transform parameters may vary at each step. Every displayed quotient denominator,
  including the denominators in the Bailey-pair relation, is required to be nonzero.
  `DLMF.QHypergeometric.IsBaileyChain` ([definition](DLMF/QHypergeometric/BaileyPairs.lean#L67)).

  [DLMF 17.12.E6](https://dlmf.nist.gov/17.12.E6):
  The explicit numerator sequence of the Rogers–Ramanujan Bailey pair.
  `DLMF.QHypergeometric.rogersBaileyAlpha` ([definition](DLMF/QHypergeometric/BaileyPairs.lean#L172)).

  [DLMF 17.12.E6](https://dlmf.nist.gov/17.12.E6):
  The explicit denominator sequence of the Rogers–Ramanujan Bailey pair.
  `DLMF.QHypergeometric.rogersBaileyBeta` ([definition](DLMF/QHypergeometric/BaileyPairs.lean#L179)).

## Chapter 18 — Orthogonal polynomials

Expanded review: all 42 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§18.1–18.42 checked; matching headings are §18.2(i),
§18.3, §18.19, §18.25, §18.33(i), §18.34(i), §18.35(i), and the three
definition paragraphs in §18.37(i)/(ii). Tables in those sections were included.

All local names in the following entries are in `DLMF.OrthogonalPolynomials`.
The orthogonality domains and parameter inequalities in the table are
mathematical assumptions, not restrictions on the types of these total functions.

### §18.1 Notation

- **Forward, backward, and imaginary central differences and their iterates**, [§18.1(i)](https://dlmf.nist.gov/18.1.i): Mathlib `fwdDiff` in [ForwardDiff](.lake/packages/mathlib/Mathlib/Algebra/Group/ForwardDiff.lean#L40) gives Δf = `fwdDiff 1 f`; ∇f = `-fwdDiff (-1) f`. The central difference is `fun x => fwdDiff Complex.I f (x - Complex.I / 2) / Complex.I`. Higher differences are function iterates. The project uses `fwdDiff (-1)` for backward Rodrigues formulas, with the resulting sign accounted for; no separate public central-difference wrapper was found. Koekoek's δ differs from DLMF's by a factor of i.

- **Finite/infinite q-Pochhammer and multi-parameter q-products**, [§18.1(i)](https://dlmf.nist.gov/18.1.i): these repeat the Chapter 17 objects `DLMF.QSeries.qPochhammer`, `qPochhammerInf` and the product-over-parameter-list conventions. Public list wrappers are `DLMF.QHypergeometric.qPochhammerList` and `qPochhammerListInf` in [Basic](DLMF/QHypergeometric/Basic/Series.lean#L23). The duplicated notation introduces no additional polynomial-specific q-product.

- **Alternative zero-parameter Gegenbauer convention**, [18.1.1](https://dlmf.nist.gov/18.1.E1): C₀⁽⁰⁾=1 and Cₙ⁽⁰⁾=2Tₙ/n for n≥1. This is an alternative convention explicitly mentioned, but not used, by DLMF. It is expressible with Mathlib's Chebyshev T; it is **not** `ultrasphPoly 0 n`, whose raw hypergeometric prefactor vanishes for positive n. No separate wrapper implements the alternative convention.

- **Shifted Jacobi polynomials**, [18.1.2](https://dlmf.nist.gov/18.1.E2): Gₙ(p,q,x)=n! Pₙ⁽ᵖ⁻ᑫ,ᑫ⁻¹⁾(2x−1)/(n+p)ₙ. This is an unnamed rescaling of `jacobiPolyP` in its regular parameter range; a finite-coefficient realization is needed at exceptional parameters. DLMF explicitly does not develop this convention further.

- **Dilated Chebyshev polynomials**, [18.1.3](https://dlmf.nist.gov/18.1.E3): Cₙ(x)=2Tₙ(x/2) and Sₙ(x)=Uₙ(x/2), expressible using Mathlib's `Polynomial.Chebyshev.T` and `U`. These are not the Gegenbauer Cₙ; no dedicated local wrappers were found. DLMF explicitly does not develop these conventions further.

### §18.2 General Orthogonal Polynomials

<!-- retained entry 120 -->
- **Orthogonality on an interval, countable set, or general measure**,
  [18.2.1–4_5 and prose](https://dlmf.nist.gov/18.2.i):
  `DLMF.OrthogonalPolynomials.IsOrthogonalPolynomials` in
  [General](DLMF/OrthogonalPolynomials/General.lean#L33), a full infinite
  sequence of real polynomials with degree, integrability, positive norm and
  pairwise orthogonality requirements. Interval weights are converted to
  measures by `weightMeasure` in
  [ClassicalInstances](DLMF/OrthogonalPolynomials/ClassicalInstances.lean#L47).
  Counting measures with weights encode discrete sets. A finite system on
  `N+1` points, 18.2.3, is not itself an instance of this infinite-sequence
  predicate; it is represented by finite orthogonality statements.

- **Squared Norm**, [DLMF 18.2.E5](https://dlmf.nist.gov/18.2.E5):
  The squared norm `h_n = ∫ p_n² dμ` (DLMF 18.2.5).
  `DLMF.OrthogonalPolynomials.squaredNorm` ([definition](DLMF/OrthogonalPolynomials/GeneralIdentities.lean#L36)).

- **First Weighted Squared Norm**, [DLMF 18.2.E6](https://dlmf.nist.gov/18.2.E6):
  The weighted squared norm `∫ x p_n² dμ` (DLMF 18.2.6).
  `DLMF.OrthogonalPolynomials.firstWeightedSquaredNorm` ([definition](DLMF/OrthogonalPolynomials/GeneralIdentities.lean#L442)).

- **Leading and next two coefficients; monic and orthonormal standardizations**, [18.2.7 and prose](https://dlmf.nist.gov/18.2.E7): kₙ is `(p n).leadingCoeff` (equivalently `coeff n` for degree n); k̃ₙ and k̃̃ₙ are `coeff (n-1)` and `coeff (n-2)` with DLMF's explicit zero conventions for n=0 and n<2. Natural subtraction alone does not implement those conventions. Monicity is Mathlib `Polynomial.Monic`; orthonormal standardization is `squaredNorm μ p n = 1` in every degree. There are no separate local wrappers for these coefficient sequences or this standardization. The constant p₀ need not be 1, while p₋₁=0 is a convention outside natural-number indexing.

- **The two sets of three-term recurrence coefficients and their monic forms**, [18.2.8–11_8](https://dlmf.nist.gov/18.2.E8): Aₙ=kₙ₊₁/kₙ, Bₙ=−Aₙ h̃ₙ/hₙ, Cₙ=(Aₙ/Aₙ₋₁)hₙ/hₙ₋₁; aₙ=1/Aₙ, bₙ=−Bₙ/Aₙ, cₙ=Cₙ/Aₙ. The diagonal bₙ has the public object `recurrenceDiagonal`; other coefficients are explicit expressions in the general recurrence statements. In monic normalization αₙ=bₙ and βₙ=hₙ/hₙ₋₁; the orthonormal family qₙ=pₙ/√hₙ is an unnamed rescaling. These sequences and families should not be conflated with their traditionally normalized versions.

  [DLMF 18.2.E11](https://dlmf.nist.gov/18.2.E11):
  The coefficient of degree `n` in `X p_n`, expanded in the OP basis.
  `DLMF.OrthogonalPolynomials.recurrenceDiagonal` ([definition](DLMF/OrthogonalPolynomials/GeneralIdentities.lean#L55)).

- **The Jacobi matrix and its finite truncation**, [18.2.11_9](https://dlmf.nist.gov/18.2.E11_9), [18.2.18](https://dlmf.nist.gov/18.2.E18): the tridiagonal matrix with diagonal bₙ, upper diagonal aₙ, and lower diagonal cₙ; symmetry means cₙ=aₙ₋₁. It can be expressed with Mathlib `Matrix`, using natural indices or `Fin n` for the truncation. No dedicated orthogonal-polynomial Jacobi-matrix definition was found. The algebraic-geometry declaration named `jacobiMatrix` is a different object.

- **Christoffel Darboux Kernel**, [DLMF 18.2.E12](https://dlmf.nist.gov/18.2.E12):
  The Christoffel–Darboux kernel `K_n(x, y) = ∑_{k ≤ n} p_k(x) p_k(y)/h_k` (DLMF 18.2.12).
  `DLMF.OrthogonalPolynomials.christoffelDarbouxKernel` ([definition](DLMF/OrthogonalPolynomials/GeneralIdentities.lean#L41)).

- **Kernel polynomials**, [18.2.14](https://dlmf.nist.gov/18.2.E14): qₙ(x;y)=Kₙ(x,y) for y outside the orthogonality interval. This is `christoffelDarbouxKernel μ p n x y`, already catalogued for 18.2.12, with the second argument fixed; no additional definition is necessary. The confluent value 18.2.13 uses the same object on the diagonal.

- **Discriminant expressed through a complete root list. The identities below**, [DLMF 18.2.E20](https://dlmf.nist.gov/18.2.E20):
  Discriminant expressed through a complete root list. The identities below
  assume positive degree; this avoids conventions for the discriminant of a constant.
  `DLMF.OrthogonalPolynomials.rootDiscriminant` ([definition](DLMF/OrthogonalPolynomials/BoundsZeros/PointwiseAndZeroBounds.lean#L1042)).

- **Quadratically transformed polynomial families and weights**, [18.2.22–23](https://dlmf.nist.gov/18.2.E22): rₙ(x²)=p₂ₙ(x), sₙ(x²)=p₂ₙ₊₁(x)/x and v(x²)=w(x), or their 2x²−1 variants. The corresponding weights are x⁻¹ᐟ²v(x), x¹ᐟ²v(x), or (1+x)⁻¹ᐟ²v(x), (1+x)¹ᐟ²v(x). No public constructors for these transformed families were found; individual classical instances are represented by the existing Jacobi/Laguerre polynomial functions. Defining s at x=0 requires polynomial extension, not totalized division by x.

- **Completeness and Fourier coefficients for a general OP system**, [§18.2(viii), 18.2.24–25](https://dlmf.nist.gov/18.2.viii): completeness means density in weighted L² of the finite linear span of the polynomials; λₙ=hₙ⁻¹∫f pₙ dμ. General Mathlib span/closure and `MeasureTheory.Lp` express this, but no separate generic OP-completeness predicate or coefficient function was found. The `IsOrthogonalPolynomials.basis` object is a basis of the polynomial vector space and does not itself assert L² completeness. Upstream family-specific objects include `TauCeti.chebyshevTHilbertBasis` and `TauCeti.gaussianHermiteHilbertBasis` in their [Chebyshev](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/HilbertBasis.lean#L88) and [Gaussian Hermite](.lake/packages/TauCeti/TauCeti/Probability/Distributions/Gaussian/Hermite/Basis.lean#L138) modules, with the normalizations of those modules.

- **Moment**, [DLMF 18.2.E26](https://dlmf.nist.gov/18.2.E26):
  The `n`-th moment `∫ xⁿ dμ` (DLMF 18.2.26).
  `DLMF.OrthogonalPolynomials.moment` ([definition](DLMF/OrthogonalPolynomials/GeneralIdentities.lean#L46)).

- **Hankel Determinant**, [DLMF 18.2.E27](https://dlmf.nist.gov/18.2.E27):
  The Hankel determinant `det (μ_{i+j})_{i,j<n}` (DLMF 18.2.27).
  `DLMF.OrthogonalPolynomials.hankelDeterminant` ([definition](DLMF/OrthogonalPolynomials/GeneralIdentities.lean#L50)).

- **Shifted Hankel Determinant**, [DLMF 18.2.E28](https://dlmf.nist.gov/18.2.E28):
  The Hankel determinant with its last column shifted by one, `0` at `n = 0`
  (DLMF 18.2.28).
  `DLMF.OrthogonalPolynomials.shiftedHankelDeterminant` ([definition](DLMF/OrthogonalPolynomials/GeneralIdentities.lean#L447)).

- **First associated monic and corecursive/numerator polynomials**, [18.2.31–33](https://dlmf.nist.gov/18.2.E31): the first associated family shifts the monic recurrence coefficients by one; the corecursive family starts with 0,1 and equals the first associated family with the degree lowered by one. These are specializations/rescalings of `associated` from [Associated](DLMF/OrthogonalPolynomials/Associated.lean#L35), not separately named definitions; the zero member must be handled separately. The integral divided-difference construction in 18.2.33 describes the same associated family. See also §18.30(vi)–(vii).

- **The J-fraction and its approximants; Christoffel numbers**, [18.2.34–37](https://dlmf.nist.gov/18.2.E34): Fₙ is the finite J-fraction, equivalently the ratio of numerator and denominator polynomials; the weights wₖ are integrals of the cardinal factors pₙ(x)/((x−xₖ)pₙ′(xₖ)). The public adapter `polynomialFraction` in [ContinuedFractions](DLMF/OrthogonalPolynomials/ContinuedFractions.lean#L31) constructs Mathlib `GenContFract` from prescribed partial numerators/denominators, and its `.nums`, `.dens`, and convergent APIs provide the finite objects. No dedicated general Christoffel-number function or normalized Stieltjes-transform wrapper was found.

- **Generalized Szegő classes**, [§18.2(xi), prose](https://dlmf.nist.gov/18.2.xi): Nevai's class S consists of orthogonality measures supported in [−1,1] whose absolutely continuous density is in the Szegő class; extensions permit outside masses satisfying Σ√(|xₖ|−1)<∞. These measure classes have no identified local predicate. `IsSzegoWeight` captures the logarithmic integral/positivity part for a density; DLMF additionally assumes the finite positive mass/moment requirements of 18.2.1_5. `IsNevaiClass` captures the two recurrence-coefficient limits of 18.2.40, without packaging a measure or the side condition a>0.

  [DLMF 18.2.E39](https://dlmf.nist.gov/18.2.E39):
  The Szegő integrability condition on `(-1,1)`, with positivity stated
  explicitly so that totalized `Real.log 0` cannot mask a zero weight.
  `DLMF.OrthogonalPolynomials.IsSzegoWeight` ([definition](DLMF/OrthogonalPolynomials/GeneralIdentities.lean#L459)).

  [DLMF 18.2.E40](https://dlmf.nist.gov/18.2.E40):
  The Nevai class `M(a, b)`: `√β_n → a/2` and `α_n → b` (DLMF 18.2.40).
  `DLMF.OrthogonalPolynomials.IsNevaiClass` ([definition](DLMF/OrthogonalPolynomials/GeneralIdentities.lean#L467)).

- **Poisson Kernel**, [DLMF 18.2.E41](https://dlmf.nist.gov/18.2.E41):
  The Poisson kernel `∑ p_n(x) p_n(y)/h_n zⁿ` (DLMF 18.2.41).
  `DLMF.OrthogonalPolynomials.poissonKernel` ([definition](DLMF/OrthogonalPolynomials/GeneralIdentities.lean#L454)).

- **Semiclassical orthogonal polynomials and structure relations**, [18.2.42–44 and prose](https://dlmf.nist.gov/18.2.E44): semiclassical means a degree-bounded polynomial differential structure relation π(x)pₙ′=Σⱼ₌ₙ₋ₛⁿ⁺ᵗ aₙⱼpⱼ, with π,s,t independent of n. The raising/lowering operators also introduce πₙ,Aₙ,Bₙ,λₙ,μₙ as coefficient data. No generic local semiclassical predicate, structure-relation object, or pair of ladder operators was found.

- **Sheffer polynomials and delta operators**, [18.2.45–46 and prose](https://dlmf.nist.gov/18.2.E45): the generating function f(t)exp(xu(t))=Σcₙpₙ(x)tⁿ/n!, with f(0)=1,u(0)=0,u′(0)=1; the inverse series v gives the lowering operator v(Dₓ). A delta operator commutes with translation and sends x to a nonzero constant. Formal series can use Mathlib `PowerSeries`; no identified Sheffer-sequence or delta-operator wrapper exists locally or in the searched polynomial APIs. The named polynomial examples are already covered in Chapters 18 and 24.

### §18.3 Definitions

- **Pseudo-Jacobi/Routh–Romanovski polynomials and their weight**, [§18.3, Jacobi on other intervals](https://dlmf.nist.gov/18.3): Pₙ⁽⁻ᴺ⁻¹⁺ⁱν,⁻ᴺ⁻¹⁻ⁱν⁾(ix), with weight (1+x²)⁻ᴺ⁻¹exp(2ν arctan x), define a finite orthogonal system. There is no separate named wrapper. The finite complex-coefficient object `DLMF.OrthogonalPolynomials.JacobiDisc.jacPoly` in [JacobiDiscriminant](DLMF/OrthogonalPolynomials/JacobiDiscriminant.lean#L48) supplies the continued polynomial at all parameters; the raw `jacobiPolyP` formula cannot automatically be substituted at singular lower parameters. Real-parameter finite polynomials are `jacobiPolyPR`. This distinction also applies to the finite Jacobi systems on (1,∞).

<!-- retained entry 121 -->
- **Jacobi**, [Table 18.3.1](https://dlmf.nist.gov/18.3.T1):
  `jacobiPolyP` in [Classical](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L43)
  is the complex hypergeometric formula; `jacobiPolyPR`, `jacobiWeight`
  and `jacobiMeasure` in
  [ClassicalInstances](DLMF/OrthogonalPolynomials/ClassicalInstances.lean#L491)
  and [Classical](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L69) supply real
  polynomial and measure objects. The continued finite coefficient formula
  handles parameters for which the raw hypergeometric quotient needs care.
  The pseudo-Jacobi/Routh–Romanovski functions mentioned at the end of §18.3
  are specializations `Pₙ^(-N-1+iν,-N-1-iν)(ix)`, without a separate local name.

<!-- retained entry 122 -->
- **Ultraspherical/Gegenbauer**, [Table 18.3.1](https://dlmf.nist.gov/18.3.T1):
  `ultrasphPoly` in [Classical](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L55)
  and real polynomial `ultrasphPolyR` in
  [ClassicalInstances](DLMF/OrthogonalPolynomials/ClassicalInstances.lean#L863).

<!-- retained entry 123 -->
- **Chebyshev T and U**, [Table 18.3.1](https://dlmf.nist.gov/18.3.T1): Mathlib
  `Polynomial.Chebyshev.T`, `Polynomial.Chebyshev.U` in
  [Chebyshev/Basic](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Basic.lean).
  Shifted T-star and U-star are evaluations at `2x-1`, without separate local
  definition objects. The finite cosine nodes in [18.3.2](https://dlmf.nist.gov/18.3.E2)
  are explicit expressions, not a separately named node function.

<!-- retained entry 124 -->
- **Chebyshev V and W**, [Table 18.3.1](https://dlmf.nist.gov/18.3.T1):
  `chebyshevV`, `chebyshevW` in [Explicit](DLMF/OrthogonalPolynomials/Explicit.lean#L54),
  with DLMF's distinct normalizations at `x=1`.

<!-- retained entry 125 -->
- **Legendre and shifted Legendre**, [Table 18.3.1](https://dlmf.nist.gov/18.3.T1):
  `legendrePolyP` in [Classical](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L50),
  the Jacobi specialization, and the corresponding real polynomial objects
  used in [Legendre](DLMF/OrthogonalPolynomials/Legendre.lean).
  Mathlib's `Polynomial.shiftedLegendre` in
  [ShiftedLegendre](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean)
  is an independent polynomial construction;
  `aeval_shiftedLegendre_eq_legendrePolyP` is the normalization/argument bridge.

<!-- retained entry 126 -->
- **Laguerre**, [Table 18.3.1](https://dlmf.nist.gov/18.3.T1):
  `laguerrePolyL` in [Classical](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L36),
  continued finite-sum `laguerreExtended` in
  [Explicit](DLMF/OrthogonalPolynomials/Explicit.lean#L35),
  `laguerrePolyLR`, `laguerreWeight`, and `laguerreMeasure` in
  [ClassicalInstances](DLMF/OrthogonalPolynomials/ClassicalInstances.lean#L366).
  `laguerreExtended` remains the polynomial at negative-integral α where
  the raw M-based definition can differ by totalization.

<!-- retained entry 127 -->
- **Hermite H and He**, [Table 18.3.1](https://dlmf.nist.gov/18.3.T1):
  physicists' `hermitePolyH` in
  [Classical](DLMF/OrthogonalPolynomials/Basic/Definitions.lean#L31) and real-coefficient
  alias `hermitePolyHR` in
  [AngularRepresentations](DLMF/OrthogonalPolynomials/Integrals/AngularRepresentations.lean#L55);
  probabilists' Mathlib `Polynomial.hermite` in
  [Hermite/Basic](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Hermite/Basic.lean).
  The weights are `exp(-x²)` and `exp(-x²/2)` respectively; these normalizations
  should not be interchanged.

- **Classical weights, squared norms and leading coefficients**, [Table 18.3.1](https://dlmf.nist.gov/18.3.T1): these are mathematical parts of the traditional definitions, in addition to the family functions. The Jacobi, Laguerre and physicists' Hermite measures have the local objects already listed. Chebyshev T has Mathlib `Polynomial.Chebyshev.measureT` in [Orthogonality](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Orthogonality.lean#L50), and its squared norm/orthonormal rescaling are `TauCeti.chebyshevTNormSq` and `TauCeti.normalizedChebyshevT` in [Measure](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Measure.lean#L138). Other table weights, including V/W, shifted T/U, Gegenbauer, Legendre and probabilists' Hermite, are displayed elementary expressions or specializations, without dedicated wrappers for every row. Table hₙ and kₙ are their explicit special-function formulas or instances of `squaredNorm` and `Polynomial.leadingCoeff`; they are not additional polynomial families.

- **Chebyshev cosine nodes**, [18.3.2](https://dlmf.nist.gov/18.3.E2): xₙ,ₘ=cos((m−1/2)π/n), with one-based m. No standalone node function was found, but Mathlib `Polynomial.Chebyshev.sumZeroes` in [ChebyshevGauss](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/ChebyshevGauss.lean#L68) uses exactly these nodes with zero-based i=m−1 and weight π/n.

### §18.5 Explicit Representations

- **Rodrigues data and finite-coefficient continuations**, [18.5.5 and Table 18.5.1](https://dlmf.nist.gov/18.5.E5), [18.5.7–13](https://dlmf.nist.gov/18.5.E7): the Rodrigues weights w, polynomial factors F and constants κₙ are the table's elementary expressions; no separate generic Rodrigues-data structure is used. The finite power-series formulas are alternative realizations of the same classical families, not additional functions. `JacobiDisc.jacPoly`/`jacobiPolyPR`, `laguerreExtended`/`laguerrePolyLR`, and real `ultrasphPolyR` are relevant finite-polynomial objects, with coefficient definitions in their respective modules. The raw complex hypergeometric realizations retain exceptional-parameter limitations.

### §18.8 Differential Equations

- **Weighted angular/radial classical polynomial functions**, [Table 18.8.1](https://dlmf.nist.gov/18.8.T1): the table includes Jacobi functions multiplied by half-angle powers, radial/exponentially weighted Laguerre functions, and exp(−x²/2)Hₙ(x), in addition to plain polynomials. `DLMF.OrthogonalPolynomials.JacobiZeroBounds.u` in [JacobiZeroBounds](DLMF/OrthogonalPolynomials/JacobiZeroBounds.lean#L43) is the angular Jacobi function with multiplier (1−cos t)^(α/2+1/4)(1+cos t)^(β/2+1/4), hence differs from the half-angle row by the constant 2^((α+β+1)/2). `HermiteFixedX.u` in [HermiteFixedX](DLMF/OrthogonalPolynomials/HermiteFixedX.lean#L37) is exactly the unnormalized weighted physicists' Hermite function. `TauCeti.hermiteFunction` in [Basic](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Basic.lean#L36) is the normalized Hermite function, implemented with probabilists' Hermite at √2x. Other table rescalings and ODE coefficients are expressions, without separate named family objects.

### §18.12 Generating Functions

- **Generating-function auxiliary square root**, [18.12.1 and 18.12.2_5](https://dlmf.nist.gov/18.12.E1): R=√(1−2xz+z²), with the branch R(0)=1. This is `Complex.sqrt (1 - 2*x*z + z^2)` on the generating-function domain, without a standalone public R definition. The generating functions themselves have the existing series and elementary/hypergeometric expressions; formal coefficient-series objects include `laguerreSeries` in [LaguerreSeries](DLMF/OrthogonalPolynomials/LaguerreSeries.lean#L34) and `gegenbauerSeries` in [GegenbauerSeries](DLMF/OrthogonalPolynomials/GegenbauerSeries.lean#L38). These are formal power series rather than additional analytic polynomial families.

### §18.14 Inequalities

- **Endpoint-normalized Jacobi polynomials and ordered extrema**, [18.14.11](https://dlmf.nist.gov/18.14.E11), [18.14.14 and 18.14.21](https://dlmf.nist.gov/18.14.E14): Rₙ(x)=Pₙ⁽α,β⁾(x)/Pₙ⁽α,β⁾(1) is an unnamed rescaling of `jacobiPolyP`. The Jacobi and Laguerre extrema xₙ,ₘ are introduced by order in the prose/formulas, not by separate local extremum-enumeration functions. Generic derivative/zero/extremum predicates describe them; a sorted sequence would require additional choices and indexing conventions.

### §18.15 Asymptotic Approximations

- **Jacobi asymptotic coefficients, phase and Bessel scaling**, [18.15.2–9](https://dlmf.nist.gov/18.15.E2): fₘ(θ), Cₘ,ℓ(α,β), θₙ,ₘ,ℓ, ρ=n+(α+β+1)/2, Aₘ(θ), Bₘ(θ), g(θ), and the remainder εₘ(ρ,θ) are defined by the displayed sums, powers, phase, expansion and leading-coefficient formulas. No complete local coefficient/remainder API was found. The scale ρ can be written using `JacobiZeroBounds.gamma`; the Darboux leading term in the current theorem is not an implementation of all these coefficient sequences. Higher A/B coefficients are referred to the cited literature rather than defined recursively on this DLMF page.

- **Ultraspherical and Legendre asymptotic phases**, [18.15.11](https://dlmf.nist.gov/18.15.E11), [18.15.13](https://dlmf.nist.gov/18.15.E13): θₙ,ₘ=(n+m+λ)θ−(m+λ)π/2 and αₙ,ₘ=(n−m+1/2)θ+(n−m/2−1/4)π. They are elementary expressions without dedicated local definitions; the surrounding coefficients are explicit Pochhammer/binomial expressions.

- **Laguerre asymptotic phases, coordinates and coefficient families**, [18.15.15–23](https://dlmf.nist.gov/18.15.E15): θₙ⁽α⁾(x)=2√(nx)−(α/2+1/4)π, ν=4n+2α+2, ξ=(√(x−x²)+arcsin√x)/2 on [0,1], and the piecewise Airy coordinate ζ of 18.15.21. The coefficient families aₘ,bₘ,Aₘ,Bₘ,Eₘ,Fₘ are the expansion coefficients with the displayed initial values. No dedicated local implementations of these Laguerre coordinate/coefficient families were found. `env J` and `env Ai` refer back to the envelope notions in Chapter 2, not to numerical approximations.

- **Hermite asymptotic frequency, phase and coefficient polynomials**, [18.15.24–27](https://dlmf.nist.gov/18.15.E24): μ=2n+1, ωₙ,ₘ(x)=√μ x−(m+n)π/2, and polynomials uₘ(x), with u₀=1,u₁=x³/6. `HermiteFixedX.freq` in [HermiteFixedX](DLMF/OrthogonalPolynomials/HermiteFixedX.lean#L44) is √μ; the phase is an unnamed elementary expression, and no all-order public uₘ family was found. The existing `HermiteFixedX.u n x` is the weighted Hermite function and is a **different** use of the letter u. The normalization λₙ is the already catalogued `hermiteLambda`; the symbol μ is later re-used as √(2n+1) in the Chapter 12 cross-reference, as the prose states explicitly.

  [DLMF 18.15.E25](https://dlmf.nist.gov/18.15.E25):
  The constant `λ_n` of DLMF 18.15.25: `Γ(n+1)/Γ(n/2+1)` for even `n` and
  `Γ(n+2)/(√(2n+1) Γ(n/2+3/2))` for odd `n`.
  `DLMF.OrthogonalPolynomials.hermiteLambda` ([definition](DLMF/OrthogonalPolynomials/HermiteFixedX.lean#L181)).

### §18.16 Zeros

- **Ordered Jacobi, Laguerre and Hermite zeros**, [18.16.1](https://dlmf.nist.gov/18.16.E1), [18.16.9](https://dlmf.nist.gov/18.16.E9), [18.16.16](https://dlmf.nist.gov/18.16.E16): Jacobi uses increasing angles θₙ,ₘ in (0,π), Laguerre increasing positive roots xₙ,ₘ, and Hermite decreasing positive roots only. No public local functions enumerating all three sets with these conventions were found; root conditions are stated directly using polynomial evaluation. The auxiliary φₘ=jα,ₘ/ρ and Hermite error εₙ,ₘ in 18.16.8/17 are also unnamed expressions. Bessel jα,ₘ and Airy aₘ are the zero families catalogued in Chapters 10 and 9.

### §18.18 Sums

- **Jacobi, Legendre, Laguerre and Hermite expansion coefficients**, [18.18.1,3,5,7](https://dlmf.nist.gov/18.18.E1): the coefficients are the relevant weight integrals divided by hₙ. `legendreCoeff` in [Legendre](DLMF/OrthogonalPolynomials/Legendre.lean#L191) implements 18.18.3. `chebyshevCoeff` in [ChebyshevExpansion](DLMF/OrthogonalPolynomials/ChebyshevExpansion.lean#L45) uses the convention 2/π times the angular cosine integral, so the Chebyshev expansion has a half-weighted constant term. No corresponding public Jacobi/Laguerre/Hermite coefficient wrappers were found; they remain explicit integral expressions. Weighted L² expansions use the same coefficient definitions, with convergence in L² rather than pointwise.

- **Bateman sum coefficients and bilinear kernels**, [18.18.24](https://dlmf.nist.gov/18.18.E24), [18.18.27–28](https://dlmf.nist.gov/18.18.E27): the Jacobi coefficients bₙ,ℓ are the displayed binomial/Pochhammer ratio, with no separate public wrapper found. The Hille–Hardy and Mehler functions are Poisson kernels with the normalization printed in their series. `DLMF.OrthogonalPolynomials.Mehler.kernel` in [Mehler](DLMF/OrthogonalPolynomials/Mehler.lean#L50) is the complex closed form (1−z²)⁻¹ᐟ² exp((2xyz−(x²+y²)z²)/(1−z²)); this is a second Lean realization of the Hermite bilinear kernel alongside the general `poissonKernel`. The Mehler series omits the √π factor present in hₙ for the unnormalized Hermite measure. No dedicated Hille–Hardy-kernel definition was found.

### §18.19 Hahn Class: Definitions

<!-- retained entry 130 -->
- **Hahn/Wilson class and lattice-difference terminology**, [§18.19 prose](https://dlmf.nist.gov/18.19):
  no separate class structure is defined. The distinction is reflected by the
  linear or quadratic polynomial arguments of the individual families.

<!-- retained entry 128 -->
- **Hahn, Krawtchouk, Meixner and Charlier**, [Tables 18.19.1–2](https://dlmf.nist.gov/18.19.T1):
  `DLMF.OrthogonalPolynomials.hahn`, `krawtchouk`, `meixner`, `charlier`
  in [HahnAndMeixner](DLMF/OrthogonalPolynomials/Hahn/HahnAndMeixner.lean#L116),
  all defined by finite hypergeometric sums. `charlierPoly` in
  [CharlierAndConnections](DLMF/OrthogonalPolynomials/Hahn/CharlierAndConnections.lean#L272)
  is a polynomial-valued realization. `hahnWeightInt` and `charlierWeightInt`
  in [HahnRodrigues](DLMF/OrthogonalPolynomials/HahnRodrigues.lean#L27) and
  [DiscreteRodrigues](DLMF/OrthogonalPolynomials/DiscreteRodrigues.lean#L30)
  are actual discrete weight objects; remaining table weights can be written
  by their displayed factorial/binomial expressions without another wrapper.

<!-- retained entry 129 -->
- **Continuous Hahn and Meixner–Pollaczek**, [18.19.1–9](https://dlmf.nist.gov/18.19.E1):
  `DLMF.OrthogonalPolynomials.continuousHahn`, `meixnerPollaczek`,
  `continuousHahnWeight`, and `meixnerPollaczekWeight` in
  [HahnAndMeixner](DLMF/OrthogonalPolynomials/Hahn/HahnAndMeixner.lean#L136).
  Continuous Hahn has four independent complex parameters in the definition;
  its positive orthogonality regime sets the latter pair to conjugates of the
  first. Meixner–Pollaczek uses DLMF's angle φ and gamma weight.

- **Four-parameter Hahn weight and tilted Gamma weight**, [18.19.2–3 and 18.19.7–8](https://dlmf.nist.gov/18.19.E2): besides the two-parameter conjugate-pair `continuousHahnWeight`, `DLMF.OrthogonalPolynomials.HahnMoments.weight` in [HahnMoments](DLMF/OrthogonalPolynomials/HahnMoments.lean#L29) keeps all four Gamma parameters independent. `DLMF.OrthogonalPolynomials.PollaczekMoments.weight` in [PollaczekMoments](DLMF/OrthogonalPolynomials/PollaczekMoments.lean#L263) is Γ(λ+ix)Γ(λ−ix)exp(θx), equal to the Meixner–Pollaczek weight after θ=2φ−π. The discrete weights, hₙ and kₙ of Tables 18.19.1–2 remain the printed elementary/Pochhammer formulas or instances of the general norm/coefficient objects; `hahnWeightInt` and `charlierWeightInt` add zero extensions off their supports.

### §18.22 Hahn Class: Recurrence Relations and
Differences

- **Normalized continuous Hahn family and difference-operator coefficients**, [18.22.4–6](https://dlmf.nist.gov/18.22.E4), [18.22.11–18](https://dlmf.nist.gov/18.22.E11): qₙ(x)=pₙ(x)/pₙ(ia), an unnamed rescaling of `continuousHahn`. The recurrence and x-difference coefficients A,C,Ã,C̃ and eigenvalues are explicit rational/polynomial/exponential expressions in the relevant statements, not new family definitions. The notation pₙ in 18.22.1/7/9/13/16 simply renames already defined families.

### §18.25 Wilson Class: Definitions

<!-- retained entry 131 -->
- **Wilson, continuous dual Hahn, Racah and dual Hahn**,
  [Table 18.25.1 and 18.25.3–15](https://dlmf.nist.gov/18.25.T1):
  `DLMF.OrthogonalPolynomials.wilson`, `continuousDualHahn`, `racah`,
  `dualHahn` in [Wilson](DLMF/OrthogonalPolynomials/Wilson.lean#L31).
  Their argument is the polynomial variable `x=y²` or
  `x=y(y+γ+δ+1)`, not y itself; the product formulas avoid choosing a square root.
  The section's gamma-ratio weights, squared norms, lattice transformations,
  and leading coefficients are explicit expressions in the local theorem
  statements, rather than additional public definition objects.

### §18.26 Wilson Class: Continued

- **The dual-Hahn-to-Meixner lattice substitution**, [18.26.12](https://dlmf.nist.gov/18.26.E12): r(x;β,c,N)=x(x+β+c⁻¹(1−c)N). This is an elementary expression used as the argument of `dualHahn`, with no additional public function definition.

### §18.27 q -Hahn Class

- **q-Hahn-class orthogonality sets, weights and norms**, [18.27.2–24](https://dlmf.nist.gov/18.27.E2): the geometric support sets X and densities vₓ/hₙ are explicit products in this section, without additional public definition objects. This includes the two big-q-Jacobi lattices and weights (18.27.8–12), little-q-Jacobi weights, continuous and bilateral discrete q-Laguerre weights with h₀⁽¹⁾/h₀⁽²⁾, the two Stieltjes–Wigert weights (q-product and log-normal), and discrete-q-Hermite I/II weights. These are mathematically different measures, not alternative names for one measure; q-Laguerre, Stieltjes–Wigert and discrete-q-Hermite II can have nonunique orthogonality measures. They are expressible with the Chapter 17 q-products and usual sums/integrals; the displayed formulas still require their parameter/domain restrictions and continuation at removable exceptional values.

- **Q Hahn**, [DLMF 18.27.E3](https://dlmf.nist.gov/18.27.E3):
  The `q`-Hahn polynomial `Q_n(x; a, b, N; q)` as a terminating `₃φ₂` (DLMF 18.27.3).
  `DLMF.OrthogonalPolynomials.qHahn` ([definition](DLMF/OrthogonalPolynomials/QFamilies/BasicIdentities.lean#L49)).

- **Big QJacobi**, [DLMF 18.27.E5](https://dlmf.nist.gov/18.27.E5):
  The big `q`-Jacobi polynomial `P_n(x; a, b, c; q)` as a terminating `₃φ₂` (DLMF 18.27.5).
  `DLMF.OrthogonalPolynomials.bigQJacobi` ([definition](DLMF/OrthogonalPolynomials/QFamilies/BasicIdentities.lean#L54)).

- **Alternative big q-Jacobi normalizations**, [18.27.6 and 18.27.6_5](https://dlmf.nist.gov/18.27.E6): Pₙ⁽α,β⁾(x;c,d;q) is the displayed q-Pochhammer multiple of `bigQJacobi (q^α) (q^β) (-q^α*d/c) q n (q^(α+1)*x/c)`; Pₙ(x;a,b,c,d;q)=`bigQJacobi a b (-a*d/c) q n (q*a*x/c)`. There are no separate local wrappers for these distinct conventions. The factors involving c and q are part of the definitions and cannot be dropped when comparing limits or orthogonality weights.

- **Little QJacobi**, [DLMF 18.27.E13](https://dlmf.nist.gov/18.27.E13):
  The little `q`-Jacobi polynomial `p_n(x; a, b; q)` as a terminating `₂φ₁` (DLMF 18.27.13).
  `DLMF.OrthogonalPolynomials.littleQJacobi` ([definition](DLMF/OrthogonalPolynomials/QFamilies/BasicIdentities.lean#L59)).

- **Little QLaguerre**, [DLMF 18.27.E14_5](https://dlmf.nist.gov/18.27.E14_5):
  The little `q`-Laguerre (Wall) polynomial, the little `q`-Jacobi polynomial with `b = 0`
  (DLMF 18.27.14_5).
  `DLMF.OrthogonalPolynomials.littleQLaguerre` ([definition](DLMF/OrthogonalPolynomials/QFamilies/BasicIdentities.lean#L64)).

- **Q Laguerre**, [DLMF 18.27.E15](https://dlmf.nist.gov/18.27.E15):
  The `q`-Laguerre polynomial `L_n^{(α)}(x; q)` as a terminating `₁φ₁` (DLMF 18.27.15).
  `DLMF.OrthogonalPolynomials.qLaguerre` ([definition](DLMF/OrthogonalPolynomials/QFamilies/BasicIdentities.lean#L69)).

- **Stieltjes Wigert**, [DLMF 18.27.E18](https://dlmf.nist.gov/18.27.E18):
  The Stieltjes–Wigert polynomial `S_n(x; q)` as an explicit finite sum (DLMF 18.27.18).
  `DLMF.OrthogonalPolynomials.stieltjesWigert` ([definition](DLMF/OrthogonalPolynomials/QFamilies/BasicIdentities.lean#L75)).

- **Discrete QHermite I**, [DLMF 18.27.E21](https://dlmf.nist.gov/18.27.E21):
  The discrete `q`-Hermite I polynomial `h_n(x; q)` as an explicit finite sum (DLMF 18.27.21).
  `DLMF.OrthogonalPolynomials.discreteQHermiteI` ([definition](DLMF/OrthogonalPolynomials/QFamilies/BasicIdentities.lean#L81)).

- **Discrete QHermite II**, [DLMF 18.27.E23](https://dlmf.nist.gov/18.27.E23):
  The discrete `q`-Hermite II polynomial `h̃_n(x; q)` as an explicit finite sum
  (DLMF 18.27.23).
  `DLMF.OrthogonalPolynomials.discreteQHermiteII` ([definition](DLMF/OrthogonalPolynomials/QFamilies/BasicIdentities.lean#L88)).

### §18.28 Askey–Wilson Class

- **Askey Wilson**, [DLMF 18.28.E1](https://dlmf.nist.gov/18.28.E1):
  Finite polynomial form. The displayed formula requires `a ≠ 0`; claims below
  retain that hypothesis rather than assigning continuation values at `a = 0`.
  `DLMF.OrthogonalPolynomials.askeyWilson` ([definition](DLMF/OrthogonalPolynomials/QFamilies/BasicIdentities.lean#L96)).

- **Askey Wilson Laurent**, [DLMF 18.28.E1_5](https://dlmf.nist.gov/18.28.E1_5):
  The Askey–Wilson polynomial in the Laurent variable `z`, `x = (z + z⁻¹)/2`, as a
  terminating `₄φ₃` (DLMF 18.28.1_5).
  `DLMF.OrthogonalPolynomials.askeyWilsonLaurent` ([definition](DLMF/OrthogonalPolynomials/QFamilies/BasicIdentities.lean#L106)).

- **Askey–Wilson weight, norms and discrete masses**, [18.28.3–6](https://dlmf.nist.gov/18.28.E3): the angular q-product quotient determines w(cos θ), including the factor 2πsin θ; h₀,hₙ are the displayed product ratios. Additional masses occur at (αq^ℓ+α⁻¹q⁻ℓ)/2 when α is a parameter of modulus greater than one and |αq^ℓ|>1. No public wrapper for the full weight/measure, norm sequence or mass set was found. Dropping sin θ changes the measure from dx to dθ.

- **The Askey–Wilson q-difference operator, recurrence coefficients and dual parameters**, [18.28.6_2–6_5](https://dlmf.nist.gov/18.28.E6_2): the full operator L consists of two shifted differences with `askeyWilsonDifferenceCoefficient` at z and z⁻¹, plus (1+abcd/q)f(z). Only the coefficient has a public wrapper; L, the recurrence coefficients aₙ/cₙ (with c₀=0), and the dual tuple ã=√(abcd/q), b̃=ab/ã, c̃=ac/ã, d̃=ad/ã are unnamed expressions. The square-root choice and nonzero parameters matter for the duality statement.

  [DLMF 18.28.E6_2](https://dlmf.nist.gov/18.28.E6_2):
  The coefficient in the Askey–Wilson q-difference operator.
  `DLMF.OrthogonalPolynomials.askeyWilsonDifferenceCoefficient` ([definition](DLMF/OrthogonalPolynomials/QFamilies/ClassicalLimits.lean#L632)).

- **Al Salam Chihara**, [DLMF 18.28.E7](https://dlmf.nist.gov/18.28.E7):
  The Al-Salam–Chihara polynomials, the Askey–Wilson polynomials with `c = d = 0`
  (DLMF 18.28.7).
  `DLMF.OrthogonalPolynomials.alSalamChihara` ([definition](DLMF/OrthogonalPolynomials/QFamilies/BasicIdentities.lean#L113)).

- **Inverse-q Al-Salam–Chihara polynomials**, [18.28.9–12](https://dlmf.nist.gov/18.28.E9): Qₙ(x;a,b|q⁻¹) is expressible as `alSalamChihara a b q⁻¹ n x` where its finite definition is regular; no separate inverse-q wrapper exists. Its infinite lattice and discrete orthogonality weights differ from the bounded-interval q-family and are not packaged as a local measure.

- **Q Gegenbauer**, [DLMF 18.28.E13](https://dlmf.nist.gov/18.28.E13):
  The Laurent form of the `q`-ultraspherical polynomials (AAR (10.11.1)),
  with `x = exp(iθ)` corresponding to the polynomial argument `cos θ`.
  `DLMF.QSeries.qGegenbauer` ([definition](DLMF/QSeries/Basic/Series.lean#L32)).

- **Continuous QHermite Laurent**, [DLMF 18.28.E16](https://dlmf.nist.gov/18.28.E16):
  Laurent argument `z`, representing the polynomial argument `(z + z⁻¹)/2`.
  `DLMF.OrthogonalPolynomials.continuousQHermiteLaurent` ([definition](DLMF/OrthogonalPolynomials/QFamilies/BasicIdentities.lean#L118)).

- **Continuous inverse-q Hermite polynomials**, [18.28.18](https://dlmf.nist.gov/18.28.E18): hₙ(sinh t|q)=i⁻ⁿHₙ(i sinh t|q⁻¹), equivalently the displayed terminating ₁φ₁/sum. This is expressible through `continuousQHermiteLaurent q⁻¹ n (i*exp t)` with the factor i⁻ⁿ, since the Laurent argument gives (z+z⁻¹)/2=i sinh t. No separate local hₙ wrapper was found. The orthogonality measure is not unique; it should not be identified with the continuous-q-Hermite measure.

- **Q Racah**, [DLMF 18.28.E19](https://dlmf.nist.gov/18.28.E19):
  The `q`-Racah polynomial `R_n(x; α, β, γ, δ | q)` as a terminating `₄φ₃` (DLMF 18.28.19).
  `DLMF.OrthogonalPolynomials.qRacah` ([definition](DLMF/OrthogonalPolynomials/QFamilies/BasicIdentities.lean#L123)).

- **Continuous q-Jacobi polynomials and normalized Askey–Wilson polynomials**, [18.28.24](https://dlmf.nist.gov/18.28.E24), [§18.28(x)](https://dlmf.nist.gov/18.28.x): Pₙ⁽α,β⁾(x|q) is (q^(α+1);q)ₙ/(q;q)ₙ times `askeyWilsonLaurent` at the four signed powers of q in 18.28.24; no standalone continuous-q-Jacobi wrapper was found. The rₙ(x;a,b,c,d|q) used in the limits is the normalized Rₙ(z) in the polynomial variable x=(z+z⁻¹)/2, distinct from the unnormalized `askeyWilson` pₙ. It can be expressed by dividing pₙ by a⁻ⁿ(ab,ac,ad;q)ₙ where regular. The continuous-q-ultraspherical specialization retains its explicit scalar factor.

- **Bannai–Ito and nonsymmetric Wilson polynomials**, [§18.28(xi), prose](https://dlmf.nist.gov/18.28.xi): Bannai–Ito polynomials are introduced as the q↓−1 limit of q-Racah polynomials; the prose also identifies an extended Dunkl-operator family with nonsymmetric Wilson polynomials. No corresponding dedicated Lean definition was found. The page gives this characterization and references, rather than an explicit formula fixing every normalization/parameter convention.

### §18.29 Asymptotic Approximations for q -Hahn and Askey–Wilson Classes

- **Leading asymptotic coefficient; its argument is on the unit circle**, [DLMF 18.29.E2](https://dlmf.nist.gov/18.29.E2):
  Leading asymptotic coefficient; its argument is on the unit circle.
  `DLMF.OrthogonalPolynomials.askeyWilsonAsymptoticCoefficient` ([definition](DLMF/OrthogonalPolynomials/QFamilies/ClassicalLimits.lean#L831)).

### §18.30 Associated OP’s

- **General associated family. The shift may be real, as in DLMF §18.30**, [DLMF 18.30.E3](https://dlmf.nist.gov/18.30.E3):
  General associated family. The shift may be real, as in DLMF §18.30.
  The `n = 0` step is written separately to avoid a negative natural index.
  `DLMF.OrthogonalPolynomials.associated` ([definition](DLMF/OrthogonalPolynomials/Associated.lean#L35)).

- **Associated Jacobi, Legendre and ultraspherical polynomials**, [18.30.4–7](https://dlmf.nist.gov/18.30.E4), [§18.30(viii)](https://dlmf.nist.gov/18.30.viii): associated Jacobi is `associated A B C c` with the traditionally normalized rational Jacobi recurrence coefficients extended to a real degree argument; Legendre sets α=β=0. There are no dedicated wrappers for these two families. Associated ultraspherical is exactly the specialization `pollaczek lam 0 0 c`. These are recurrence-index shifts and differ from the associated Legendre/Ferrers functions of Chapter 14. Removable initial coefficient values of the classical Jacobi recurrence need the continuity conventions stated in §18.9.

- **Associated Laguerre**, [DLMF 18.30.E9](https://dlmf.nist.gov/18.30.E9):
  The associated Laguerre polynomials `L_n^{(λ)}(x; c)`, defined by the shifted Laguerre
  recurrence (DLMF 18.30.9).
  `DLMF.OrthogonalPolynomials.associatedLaguerre` ([definition](DLMF/OrthogonalPolynomials/Associated.lean#L44)).

- **Associated Laguerre, Hermite and Meixner–Pollaczek orthogonality weights**, [18.30.11](https://dlmf.nist.gov/18.30.E11), [18.30.15](https://dlmf.nist.gov/18.30.E15), [18.30.18](https://dlmf.nist.gov/18.30.E18): respectively x^λe⁻ˣ/|U(c,1−λ,xe⁻ⁱπ)|², |U(c−1/2,i√2x)|⁻² with parabolic-cylinder U, and the printed Gamma/exponential/hypergeometric quotient. No public local wrappers were found. The two meanings of U must be distinguished; the first uses a boundary value on the lower side of the confluent-U cut, not a naive substitution into a principal-branch totalized function at negative real x. In other parameter regimes discrete masses may supplement the continuous part.

- **Associated Hermite**, [DLMF 18.30.E13](https://dlmf.nist.gov/18.30.E13):
  The associated Hermite polynomials `H_n(x; c)`, defined by the shifted Hermite recurrence
  (DLMF 18.30.13).
  `DLMF.OrthogonalPolynomials.associatedHermite` ([definition](DLMF/OrthogonalPolynomials/Associated.lean#L51)).

- **Associated Meixner Pollaczek**, [DLMF 18.30.E16](https://dlmf.nist.gov/18.30.E16):
  The associated Meixner–Pollaczek polynomials `P_n^{(λ)}(x; φ, c)`, defined by the
  shifted recurrence (DLMF 18.30.16).
  `DLMF.OrthogonalPolynomials.associatedMeixnerPollaczek` ([definition](DLMF/OrthogonalPolynomials/Associated.lean#L57)).

- **Corecursive, associated monic and higher corecursive families; their convergents**, [18.30.21–31](https://dlmf.nist.gov/18.30.E21): traditional corecursive polynomials start with 0,A₀ and obey the original recurrence; for n≥1 they are A₀ times the degree-(n−1) first-associated family. The monic associated family uses `associated (fun _ => 1) (fun t => -α t) β c`; corecursive order k has initial 0,1 and equals the associated family of order k+1 with degree lowered by one. Fₙ(x,k) is their ratio. No dedicated corecursive/higher-convergent public definitions were found. Natural-index zero cases require a separate branch, and the continued-fraction adapter `polynomialFraction` supplies a separate representation of the same finite ratios.

### §18.31 Bernstein–Szegő Polynomials

- **Bernstein–Szegő polynomials and their three weights**, [§18.31](https://dlmf.nist.gov/18.31): OP systems for positive polynomial ρ on [−1,1], with weights (1−x²)⁻¹ᐟ²/ρ(x), (1−x²)¹ᐟ²/ρ(x), or (1−x)¹ᐟ²(1+x)⁻¹ᐟ²/ρ(x). No dedicated local family constructor or class predicate was found. The generic `IsOrthogonalPolynomials` predicate can state the orthogonality, but does not select a normalization or construct these polynomials. Mathlib's Bernstein basis polynomials are different objects.

### §18.32 OP’s with Respect to Freud Weights

- **Ordinary/generalized Freud classes and half-Freud/Rys terminology**, [18.32.1–2 and prose](https://dlmf.nist.gov/18.32.E1): `freudWeight 0 Q x` gives exp(−Q(x)), and `freudWeight α Q x` gives |x|^αexp(−Q(x)). The DLMF regularity, evenness, nonnegativity, monotonicity and growth conditions on Q, and α>−1, are not built into this total function. No `IsFreudWeight` predicate or corresponding OP constructor was found. The half-Freud and Rys labels refer to restricted integration domains, not new formulas. The quartic instance is also represented by `DLMF.Painleve.freudMoment`, `freudHankel` and `freudRecurrenceSq` in [SolutionsDefs](DLMF/Painleve/Basic/Solutions.lean#L227); those are moment/determinant/recurrence objects rather than a separate polynomial family.

- **Freud Weight**, [DLMF 18.32.E2](https://dlmf.nist.gov/18.32.E2):
  The Freud weight `|x|^α e^{-Q(x)}` (DLMF 18.32.2).
  `DLMF.OrthogonalPolynomials.freudWeight` ([definition](DLMF/OrthogonalPolynomials/Associated.lean#L83)).

### §18.33 Polynomials Orthogonal on the Unit Circle

<!-- retained entry 132 -->
- **Unit-circle orthogonal/orthonormal polynomial systems**,
  [18.33.1](https://dlmf.nist.gov/18.33.E1):
  `DLMF.OrthogonalPolynomials.IsUnitCircleOP` in
  [UnitCircle](DLMF/OrthogonalPolynomials/UnitCircle.lean#L38) specifies
  **monic** orthogonal polynomials for a probability measure on the circle.
  DLMF's displayed system is orthonormal; norm rescaling is needed to obtain
  that normalization. `IsUnitCircleOP.ip` is the measure inner product.

- **Orthonormal OPUC, leading coefficients and line-weight transforms**, [18.33.1–3](https://dlmf.nist.gov/18.33.E1), [18.33.7](https://dlmf.nist.gov/18.33.E7), [18.33.17–19](https://dlmf.nist.gov/18.33.E17): DLMF's φₙ is orthonormal, with positive leading coefficient κₙ; the project's `IsUnitCircleOP` packages monic Φₙ and a probability measure. Thus φₙ=κₙΦₙ, where κₙ is the inverse square root of its squared norm. κₙ and the line weights w₁=(1−x²)⁻¹ᐟ²w(x+i√(1−x²)), w₂=(1−x²)¹ᐟ²w(x+i√(1−x²)) have no dedicated wrappers. Reflection of both φ and Φ is handled by `reflectedPolynomial`. The unit-circle inner product is also a public object `IsUnitCircleOP.ip` in [UnitCircle](DLMF/OrthogonalPolynomials/UnitCircle.lean#L70).

  [DLMF 18.33.E22](https://dlmf.nist.gov/18.33.E22):
  Reverse-conjugation at a specified degree; meaningful even if the constant
  coefficient vanishes.
  `DLMF.OrthogonalPolynomials.reflectedPolynomial` ([definition](DLMF/OrthogonalPolynomials/UnitCircle.lean#L32)).

- **Trivial, Szegő–Askey, q-Askey and Rogers–Szegő cases and weights**, [18.33.12–16](https://dlmf.nist.gov/18.33.E12): the trivial polynomials are zⁿ with w=1; Szegő–Askey has weight (1−(z+z⁻¹)/2)^λ and its two Jacobi line weights; q-Askey has |(qz;q²)∞/(aqz;q²)∞|². These weights occur explicitly in `szegoAskey_orthogonal` and `szegoAskeyQ_orthogonal`, not in separate weight definitions. The Rogers–Szegő case is `szegoAskeyQ 0 q n z`; its argument includes the q⁻¹ scaling in DLMF's convention. The displayed finite-sum families are not unit-normalized φₙ without further scalar factors.

- **Szego Askey**, [DLMF 18.33.E13](https://dlmf.nist.gov/18.33.E13):
  The Szegő–Askey polynomials `∑_k (λ+1)_k (λ)_{n-k} / (k! (n-k)!) zᵏ` (DLMF 18.33.13).
  `DLMF.OrthogonalPolynomials.szegoAskey` ([definition](DLMF/OrthogonalPolynomials/UnitCircle.lean#L53)).

- **Szego Askey Q**, [DLMF 18.33.E15](https://dlmf.nist.gov/18.33.E15):
  The `q`-analogue of the Szegő–Askey polynomials (DLMF 18.33.15).
  `DLMF.OrthogonalPolynomials.szegoAskeyQ` ([definition](DLMF/OrthogonalPolynomials/UnitCircle.lean#L59)).

- **Verblunsky Coefficient**, [DLMF 18.33.E25](https://dlmf.nist.gov/18.33.E25):
  The Verblunsky coefficient `α_n = -conj(φ_{n+1}(0))` of a monic OPUC sequence
  (DLMF 18.33.25).
  `DLMF.OrthogonalPolynomials.verblunskyCoefficient` ([definition](DLMF/OrthogonalPolynomials/UnitCircle.lean#L48)).

- **The OPUC recurrence parameter ρₙ**, [18.33.26](https://dlmf.nist.gov/18.33.E26): ρₙ=√(1−|αₙ|²)=κₙ/κₙ₊₁, expressible as `Real.sqrt (1 - ‖verblunskyCoefficient p n‖^2)`. There is no separate public ρₙ definition; `unitCircle_norm_ratio` states the related squared-norm identity. The biorthogonal and rational families in §18.33(v) are literature pointers, without a formula or identified local family definition.

### §18.34 Bessel Polynomials

<!-- retained entry 133 -->
- **Generalized Bessel yₙ(x;a), ordinary yₙ and reverse θₙ**,
  [18.34.1–3](https://dlmf.nist.gov/18.34.E1):
  `DLMF.OrthogonalPolynomials.besselPolynomial` and `reverseBesselPolynomial`
  in [Associated](DLMF/OrthogonalPolynomials/Associated.lean#L72).
  The first uses DLMF's parameter a (not the shifted convention a-2 of
  Koekoek et al.); a=2 gives ordinary y. The reversal is a finite polynomial,
  so its zero value is retained. Two-parameter `(a,b)` variants are argument
  rescalings, without separate named definitions.

- **Generalized/reverse Bessel rescalings and Romanovski–Bessel systems**, [18.34.2–3](https://dlmf.nist.gov/18.34.E2), [18.34.5_5](https://dlmf.nist.gov/18.34.E5_5): yₙ(x;a,b)=`besselPolynomial a n (2*x/b)`; θₙ(x;a,b)=xⁿyₙ(x⁻¹;a,b), with polynomial extension at zero. The existing `reverseBesselPolynomial` implements the ordinary a=b=2 case by a finite polynomial formula valid at zero. Romanovski–Bessel denotes the finite positive-measure system for a<1, with weight x^(a−2)e^(−2/x); it is the same yₙ family, not a new public function. The general reverse/rescaled families and their signed moment/unit-circle weights have no standalone wrapper.

- **Finite family related to the Morse differential equation**, [DLMF 18.34.E7_1](https://dlmf.nist.gov/18.34.E7_1):
  The finite family related to the Morse differential equation.
  `DLMF.OrthogonalPolynomials.morsePolynomialFunction` ([definition](DLMF/OrthogonalPolynomials/Associated.lean#L1105)).

### §18.35 Pollaczek Polynomials

<!-- retained entry 134 -->
- **Three Pollaczek types and associated type 2/type 3**,
  [18.35.0_5–2](https://dlmf.nist.gov/18.35.E0_5):
  `DLMF.OrthogonalPolynomials.pollaczek` in
  [Associated](DLMF/OrthogonalPolynomials/Associated.lean#L65), with complex
  `λ,a,b`, real shift c, and natural degree. Set c=0 for type 2 and additionally
  λ=1/2 for type 1. The degree -1 initial value is implicit in the recurrence;
  there is no negative-degree function argument.

<!-- retained entry 135 -->
- **Monic Pollaczek Q and angular τ**, [18.35.2_2](https://dlmf.nist.gov/18.35.E2_2),
  [18.35.3](https://dlmf.nist.gov/18.35.E3): Q is the displayed Pochhammer
  rescaling of `pollaczek`, without a separate function; τ is
  `DLMF.OrthogonalPolynomials.pollaczekTau` in
  [Associated](DLMF/OrthogonalPolynomials/Associated.lean#L1084).

- **Pollaczek Angular Weight**, [DLMF 18.35.E6](https://dlmf.nist.gov/18.35.E6):
  Angular density, including the Jacobian `sin θ` for `x = cos θ`.
  `DLMF.OrthogonalPolynomials.pollaczekAngularWeight` ([definition](DLMF/OrthogonalPolynomials/Associated.lean#L1088)).

- **Pollaczek discrete mass points and weights; type-3 continuous weight**, [18.35.6_4](https://dlmf.nist.gov/18.35.E6_4), [18.35.6_6](https://dlmf.nist.gov/18.35.E6_6): D is the explicit sequence xₖ expressed using Δ=√((λ+k)²+b²−a²) and ρ=(Δ−b)/(λ+k−a); wₓₖ is its printed Gamma/power expression. The type-3 weight adds a hypergeometric denominator to the type-2 Gamma weight. No public definitions for these masses, auxiliaries or the type-3 weight were found. `pollaczekAngularWeight` represents only the continuous type-2 density **including** the sin θ Jacobian, so it is not directly the x-density w of 18.35.6 and does not package the supplemented discrete measure.

### §18.36 Miscellaneous Polynomials

- **Jacobi-type, Sobolev, multiple and matrix orthogonal polynomials**, [§18.36(i)–(iv)](https://dlmf.nist.gov/18.36.i): Jacobi-type adds endpoint Dirac masses to a Jacobi measure; Sobolev OPs use a derivative-dependent inner product; multiple OPs impose orthogonality against several measures; matrix OPs are matrix-valued with a matrix of measures. No dedicated local predicates/family constructors were found. Endpoint measures can be expressed with `Measure.dirac` plus the existing Jacobi measure, but the generic infinite scalar OP predicate does not implement the other three generalized notions.

- **Exceptional type-I/type-III index conventions, Laguerre operator and Hermite weight**, [§18.36(vi), 18.36.7–10](https://dlmf.nist.gov/18.36.vi): type-I Xₘ omits degrees 0,…,m−1, while type-III Xₘ omits degrees 1,…,m. The project implements the displayed X₁ Laguerre and X₂ Hermite examples, with shifted natural/Option indices already noted, but no generic exceptional-family predicate. Tₖ(y)=−xy″+(x−k)((x+k+1)y′−y)/(x+k) is an unnamed rational differential operator. The Hermite weight exp(−x²)/(4x²+2)² is explicit in `exceptionalHermite_orthonormal`, not a public definition. The Wronskian formula uses the same Hermite family and the Chapter 1 Wronskian notion.

- **Exceptional Laguerre Weight**, [DLMF 18.36.E3](https://dlmf.nist.gov/18.36.E3):
  The exceptional Laguerre weight `x^k e^{-x}/(x+k)²` (DLMF 18.36.3).
  `DLMF.OrthogonalPolynomials.exceptionalLaguerreWeight` ([definition](DLMF/OrthogonalPolynomials/Associated.lean#L93)).

- **Exceptional Laguerre**, [DLMF 18.36.E5](https://dlmf.nist.gov/18.36.E5):
  Degree `n + 1`: exceptional Laguerre has no degree-zero member.
  `DLMF.OrthogonalPolynomials.exceptionalLaguerre` ([definition](DLMF/OrthogonalPolynomials/Associated.lean#L88)).

- **Exceptional Hermite degrees are 0, 3, 4, …; the index type omits 1 and 2**, [DLMF 18.36.E9](https://dlmf.nist.gov/18.36.E9):
  The exceptional Hermite degrees are 0, 3, 4, …; the index type omits 1 and 2.
  `DLMF.OrthogonalPolynomials.exceptionalHermite` ([definition](DLMF/OrthogonalPolynomials/Associated.lean#L97)).

### §18.37 Classical OP’s in Two or More Variables

<!-- retained entry 136 -->
- **Disk polynomials**, [18.37.1](https://dlmf.nist.gov/18.37.E1),
  [equivalent characterization 18.37.3–5](https://dlmf.nist.gov/18.37.E3):
  `DLMF.OrthogonalPolynomials.diskPolynomial` in
  [Multivariate](DLMF/OrthogonalPolynomials/Multivariate.lean#L35), defined by
  the explicit polynomial in z and conjugate z from 18.37.6. The polar Jacobi
  formula and orthogonality characterization are bridges, not additional definitions.

- **Disk and triangle weights; root-system families**, [18.37.2](https://dlmf.nist.gov/18.37.E2), [18.37.8](https://dlmf.nist.gov/18.37.E8), [§18.37(iii)](https://dlmf.nist.gov/18.37.iii): disk density (1−x²−y²)^α and triangle density (1−x)^α(x−y)^βy^γ are explicit expressions, without standalone public measure definitions. The root-system prose names Jack polynomials, Jacobi polynomials associated with root systems, Macdonald polynomials for Aₙ/general root systems, and Macdonald–Koornwinder polynomials. No corresponding Lean family definition was identified; these are further named multivariable families, not synonyms for the implemented two-variable disk/triangle functions.

<!-- retained entry 137 -->
- **Triangle polynomials**, [18.37.7](https://dlmf.nist.gov/18.37.E7):
  `DLMF.OrthogonalPolynomials.trianglePolynomial` in
  [Multivariate](DLMF/OrthogonalPolynomials/Multivariate.lean#L42), with `n ≤ m`
  and the DLMF triangle `0 < y < x < 1`. Its product formula involves `y/x`;
  the totalized boundary value is not automatically the polynomial extension.

### §18.38 Mathematical Applications

- **Toda/Hermite rational solution**, [18.38.1](https://dlmf.nist.gov/18.38.E1): Vₙ(x)=2n Hₙ₊₁(x)Hₙ₋₁(x)/Hₙ(x)² is an unnamed expression using `hermitePolyH`. No dedicated Vₙ wrapper was found. This is in an applications section; the formula is recorded for the definitions inventory without adding a new application theorem target.

- **Symmetric Laurent polynomials, q-commutator, Askey–Wilson/Zhedanov algebra and Casimir operator**, [18.38.4–9 and prose](https://dlmf.nist.gov/18.38.E4): f(z)=c₀+Σcₖ(zᵏ+z⁻ᵏ); K₀ is the Askey–Wilson operator L, K₁ multiplies by z+z⁻¹, K₂=[K₀,K₁]q, with [X,Y]q=√q XY−q⁻¹ᐟ²YX. The constants B,C₀,C₁,D₀,D₁ are the displayed expressions in elementary symmetric polynomials e₁,…,e₄; Q is the displayed cubic/quadratic Casimir and Q₀ its scalar value. AW(3) is the abstract associative algebra with those generators/relations before specializing the constants. No dedicated Lean algebra/operator objects were found; generic Laurent polynomials, linear endomorphisms, elementary symmetric polynomials and algebra presentations provide ingredients. These mathematical definitions occur in application notes and are not new acquisition targets under project scope.

- **Dunkl operators and nonsymmetric families**, [18.38.10–11 and prose](https://dlmf.nist.gov/18.38.E10): the one-variable operator is f′(x)+(α+1/2)(f(x)−f(−x))/x; its displayed eigenfunction uses Bessel J. Nonsymmetric Askey–Wilson functions are linear combinations of Rₙ(z) and z⁻¹(1−az)(1−bz)Rₙ₋₁(z;qa,qb,c,d|q). The rational/trigonometric/q Dunkl operators, double affine Hecke algebra, nonsymmetric Wilson/Jacobi families and this eigenfunction have no identified dedicated Lean wrappers. The existing Bessel and Askey–Wilson functions supply components. These are definitions referenced in application notes, not new acquisition targets.

### §18.39 Applications in the Physical Sciences

- **Schrödinger Hamiltonians, states and physical potentials**, [18.39.7–20](https://dlmf.nist.gov/18.39.E7): the section defines one-/three-dimensional Hamiltonians, stationary/time-dependent states, their expansion coefficients, harmonic and Morse potentials, and a rational SUSY potential. The harmonic eigenfunctions are normalized weighted/scaled `hermitePolyH` functions (the normalized unscaled mathematical family is also `TauCeti.hermiteFunction`); Morse states rescale `morsePolynomialFunction`; the rational example multiplies `exceptionalHermite` by the square root of its weight. No complete local physical-state/Hamiltonian interface was identified. These named mathematical expressions are recorded as **application notes excluded from new theorem acquisition**; the existing polynomial/weight definitions remain in scope.

- **Radial/spherical-radial Coulomb functions and associated Coulomb–Laguerre polynomials**, [18.39.24–42](https://dlmf.nist.gov/18.39.E24): the radial Rₙ,ₗ and spherical-radial ψₙ,ₗ=rRₙ,ₗ use different measures r²dr and dr. The alternate Bohr index is n=p+l+1 and the radial coordinate is ρₙ=2Zr/n. The associated Coulomb–Laguerre polynomials are derivatives of p!Lₚ⁽⁰⁾, explicitly L-boldₚ₊ₘᵐ(ρ)=(−1)ᵐ(p+m)!Lₚ⁽ᵐ⁾(ρ), so they are rescalings of `laguerreExtended` in a regular regime, **not** `associatedLaguerre` from §18.30. No dedicated wrappers for these physical conventions were found. They occur in application notes excluded from new acquisition targets; Chapter 33 supplies related Coulomb functions separately.

- **Named nonclassical weight systems in Table 18.39.1**, [18.39 Table 1](https://dlmf.nist.gov/18.39.T1): Freud-bimodal exp(−(x⁴/4−x²/2)/α), quartic Freud exp(−x⁴/4−zx²), half-Freud Druvesteyn exp(−x⁴), half-Freud Gaussian exp(−(x−x₀)²), half-Freud Maxwell xᵖexp(−x²), half-Rys exp(−αx²), multi-exponential (log x)², and radiative-transfer exp(−α/x), on their listed real-line/half-line/unit-interval domains. The symbols Bₙ,pₙ,Dₙ,Gₙ,Mₙᵖ,Rₙ,MExpₙ label the corresponding OP systems without fixing a full normalization. These weights can be written as elementary functions, with several instances covered by `freudWeight`; no separate named local OP constructors were found. The quartic moments/recurrence are also in `DLMF.Painleve.SolutionsDefs`. The table is an application note excluded from new theorem acquisition; decimal numerical work is separately excluded.

- **Laguerre basis functions and Coulomb–Pollaczek conventions**, [18.39.44–54](https://dlmf.nist.gov/18.39.E44): φₙ,ₗ(sr)=(sr)ˡ⁺¹e⁻ˢʳᐟ²Lₙ⁽²ˡ⁺¹⁾(sr); CP polynomials are `pollaczek (l+1) (2*Z/s) (-2*Z/s) 0 n x`. The maps a=2Z/s, x(ε)=(8ε−s²)/(8ε+s²) and its inverse are elementary expressions. The continuous CP weight, attractive discrete mass points/weights and auxiliary θ=arccos x, τ=−(2Z/s)√((1−x)/(1+x)), ρ are explicit specializations/rescalings of the §18.35 data, not packaged as local CP measure definitions. Finite/infinite scattering-state expansions Ψ are additional application expressions, without identified wrappers. These are recorded as application-note definitions excluded from new theorem acquisition.

### §18.40 Methods of Computation

- **Determinate/indeterminate moment problem**, [§18.40(ii), prose](https://dlmf.nist.gov/18.40.ii): determinacy asks uniqueness of the positive measure with the prescribed power moments, and indeterminacy means nonuniqueness. The moments themselves are `moment`; no general local predicate packaging this moment problem was found. This mathematical notion is distinct from the numerical inversion schemes discussed subsequently.

- **Gordon P-array and recurrence coefficients from moments**, [18.40.1–3](https://dlmf.nist.gov/18.40.E1): P₁,₁=1, Pₘ,₁=0 for m>1, Pₘ,₂=(−1)ᵐ⁻¹μₘ₋₁, Pₘ,ₙ=P₁,ₙ₋₁Pₘ₊₁,ₙ₋₂−P₁,ₙ₋₂Pₘ₊₁,ₙ₋₁. The first row defines a₁=μ₀ and aₙ=P₁,ₙ₊₁/(P₁,ₙP₁,ₙ₋₁), followed by α₀=a₂, αₙ=a₂ₙ₊₁+a₂ₙ₊₂, βₙ=a₂ₙa₂ₙ₊₁. No named local P-array/Gordon-algorithm wrapper was found. These exact recursive objects are recorded independently of the excluded decimal-accuracy claims of the numerical discussion.

- **Normalized Stieltjes transform, finite quadrature transform and histogram measure**, [18.40.4–7](https://dlmf.nist.gov/18.40.E4): F(z)=μ₀⁻¹∫w(x)/(z−x)dx, F_N(z)=μ₀⁻¹Σwₙ/(z−xₙ), and μ_N(x)=ΣwₙH(x−xₙ). These are explicit integral/finite-sum expressions, with the Heaviside H from §1.16; no dedicated local wrappers were found. The histogram is equally the cumulative function of the finite atomic measure Σwₙδₓₙ. Approximate analytic continuation, printed digit counts, and numerical histogram/derivative-rule accuracy claims are excluded as numerical approximation.

- **Pointwise continued-fraction interpolation of nodes**, [18.40.9–10](https://dlmf.nist.gov/18.40.E9): x(t,N) is the displayed finite continued fraction with partial factors aₖ(t−k); a₁=x₁,N/x₂,N−1 and the remaining aℓ are given recursively by 18.40.10. No dedicated PWCF interpolation constructor was found; Mathlib's `GenContFract` and the local `polynomialFraction` adapter provide finite continued-fraction ingredients. This exact definition is recorded separately from the derivative-rule conjectural/numerical approximation 18.40.8 and its decimal examples, which are excluded.

## Chapter 19 — Elliptic integrals

Expanded review: all 39 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§19.1–19.39 checked; matching sections are §19.2 and §19.16.

### §19.1 Special Notation

- **Modulus, complementary modulus and parameter**, [DLMF 19.1](https://dlmf.nist.gov/19.1):
  The parameter is m=k²; the complementary modulus satisfies k′²=1−k². The principal complex choice is `DLMF.JacobiElliptic.jacobiComodulusk` ([source](DLMF/JacobiElliptic/Basic/Definitions.lean#L106)). A consistent other square-root choice must be tracked separately. The complementary integrals in §19.2 have their own continuation conventions, as recorded at §19.2.

### §19.2 Definitions

<!-- retained entry 138 -->
- **General elliptic integral**, [19.2.1–3 and prose](https://dlmf.nist.gov/19.2.i):
  no general Lean structure for the class of rational integrands on a
  cubic/quartic square-root curve. The particular functions below are defined.

<!-- retained entry 139 -->
- **Legendre incomplete F, E, D and Π**, [19.2.4–7](https://dlmf.nist.gov/19.2.E4):
  `DLMF.EllipticIntegrals.incEllIntFk`, `incEllIntEk`, `incEllIntDk`,
  `incEllIntPik` in [Legendre](DLMF/EllipticIntegrals/Legendre.lean#L147),
  complex segment integrals using principal square roots and a principal-value
  construction for interior Π poles. The Π argument is the characteristic
  `α²` itself, followed by modulus k. Independent real parameter-m integrals
  are `DLMF.Elliptic.Real.incEllIntFm`, `incEllIntEm` in
  [Jacobi](DLMF/Elliptic/Basic/Integrals.lean#L48), and `incEllIntPim` in
  [ThirdKind](DLMF/Elliptic/Basic/Integrals.lean#L61), with `m=k²`.
  lean-codes also defines real modulus-k F, E, Π as
  `Carlson.Real.incEllIntFk`, `incEllIntEk`, `incEllIntPik` in
  [Carlson/Elliptic/Standard](../lean-codes/Carlson/Elliptic/Standard.lean#L78).
  The ordinary real Π interval integrals do not implement principal values.

<!-- retained entry 140 -->
- **Complete K, E, D and Π**, [19.2.8](https://dlmf.nist.gov/19.2.E8):
  `DLMF.JacobiElliptic.compEllIntKk` in
  [Definitions](DLMF/JacobiElliptic/Basic/Definitions.lean#L93) is a complex
  t-integral; `DLMF.EllipticIntegrals.compEllIntEk`, `compEllIntDk`,
  `compEllIntPik` in [Legendre](DLMF/EllipticIntegrals/Legendre.lean#L180)
  specialize the amplitude to π/2. Real parameter-m K/E are
  `DLMF.Elliptic.Real.compEllIntKm`, `compEllIntEm` in
  [Complete](DLMF/Elliptic/Basic/Integrals.lean#L38), and real Π is
  `DLMF.Elliptic.Real.compEllIntPim` in [ThirdKind](DLMF/Elliptic/Basic/Integrals.lean#L68).
  lean-codes has independent real modulus-k `Carlson.Real.compEllIntKk`,
  `compEllIntEk` in [Standard](../lean-codes/Carlson/Elliptic/Standard.lean#L93).

<!-- retained entry 141 -->
- **Complementary K-prime and E-prime**, [19.2.8_1–9](https://dlmf.nist.gov/19.2.E8_1):
  `DLMF.JacobiElliptic.compEllIntKpk` is the literal complementary-modulus
  integral; `DLMF.EllipticIntegrals.cCompEllIntKk`, `cCompEllIntEk` in
  [Legendre](DLMF/EllipticIntegrals/Legendre.lean#L197) include the extra
  continuation terms on the left half-plane. These are materially different
  branch constructions, not interchangeable aliases for `K(sqrt(1-k²))`.

<!-- retained entry 142 -->
- **Bulirsch cel, el1, el2 and el3**, [19.2.11–16](https://dlmf.nist.gov/19.2.E11):
  `DLMF.EllipticIntegrals.bulirschCel`, `bulirschEl1`, `bulirschEl2`,
  `bulirschEl3` in [Legendre](DLMF/EllipticIntegrals/Legendre.lean#L222).
  The complementary modulus is complex; coefficients/characteristic p are real
  where typed so, and the specified singular cases use principal values.

<!-- retained entry 143 -->
- **Elementary degenerate RC**, [19.2.17](https://dlmf.nist.gov/19.2.E17):
  `DLMF.EllipticIntegrals.symEllIntRC` in
  [Symmetric](DLMF/EllipticIntegrals/Symmetric.lean#L132), with a Cauchy
  principal value for negative real y. `Carlson.TwoVariable.carlsonRC` in
  [QuadraticHybrid](../lean-codes/Carlson/TwoVariable/QuadraticHybrid.lean#L225)
  is an independent R-function specialization, with its own slit-domain use.

### §19.5 Maclaurin and Related Expansions

- **Hypergeometric-series construction of complete elliptic K**, [DLMF 19.5.E1](https://dlmf.nist.gov/19.5.E1): The complete elliptic integral of the first kind as the hypergeometric series of AAR §3.2, in the modulus `k`: `K = (π/2) ₂F₁(1/2, 1/2; 1; k²)`, meaningful for `‖k‖ < 1`. The real integral form in the parameter `m = k²` is `DLMF.Elliptic.Real.compEllIntKm`.
  [`DLMF.Hypergeometric.compEllIntKkSeries`](DLMF/Hypergeometric/Identities/Whipple.lean#L383).

- **Nome and small-modulus auxiliary parameters**, [DLMF 19.5.E5](https://dlmf.nist.gov/19.5.E5):
  q=exp(−πK′/K) is `DLMF.JacobiElliptic.jacobiNomek` ([source](DLMF/JacobiElliptic/Basic/Definitions.lean#L113)); the τ-parametrized version uses exp(iπτ). The r=k²/16 and λ=(1−√k′)/(2(1+√k′)) of 19.5.6–7 are local expressions in the expansion statements, without separately named constructions. The complete hypergeometric-series representative is also `DLMF.Hypergeometric.compEllIntKkSeries` ([source](DLMF/Hypergeometric/Identities/Whipple.lean#L383)); convergence and its bridge to the integral require their stated domain.

- **Descending Landen modulus sequence**, [DLMF 19.5.E11](https://dlmf.nist.gov/19.5.E11): The descending Landen sequence of moduli of DLMF 19.5.11: `k₀ = k`, `k_{m+1} = (1 - √(1 - k_m²))/(1 + √(1 - k_m²))` (principal square roots).
  [`DLMF.EllipticIntegrals.landenModulusSeq`](DLMF/EllipticIntegrals/Expansions.lean#L251).

### §19.6 Special Cases

- **The Legendre square-root factor Δ**, [DLMF 19.6.iv](https://dlmf.nist.gov/19.6.iv):
  Δ(φ,k)=√(1−k²sin²φ) has several existing implementations: `DLMF.EllipticIntegrals.p19lR1_Δ` ([source](DLMF/EllipticIntegrals/SpecialCases.lean#L171)), `DLMF.EllipticIntegrals.p19lR1_Δc` ([source](DLMF/EllipticIntegrals/Derivatives.lean#L389)), and the real `DLMF.EllipticIntegrals.ei19b_delta` ([source](DLMF/EllipticIntegrals/Addition.lean#L50)). The first takes a real angle and complex modulus, the second complex arguments, and the last real arguments. Principal complex and nonnegative real roots should not be silently identified outside their domains.

### §19.7 Connection Formulas

- **Reciprocal-modulus and quadratic-transformation parameters**, [DLMF 19.7.E6](https://dlmf.nist.gov/19.7.E6):
  κ=1/k, κ′=i k′/k, the transformed amplitude θ determined by sin θ=k sin φ, and the transformed characteristic α₁²=α²/k² occur as expressions in the connection identities. The descending and ascending Landen moduli of §19.8 are separately `DLMF.JacobiElliptic.jacobiLandenDescModulus`, `DLMF.JacobiElliptic.jacobiLandenAscModulus`, and `DLMF.JacobiElliptic.jacobiLandenAscComodulus` ([source](DLMF/JacobiElliptic/Landen.lean#L30)); amplitude and characteristic changes remain expressions in the corresponding elliptic-integral theorem statements.

### §19.8 Quadratic Transformations

- **Arithmetic-geometric mean and its iterations**, [DLMF 19.8.i](https://dlmf.nist.gov/19.8.i):
  Mathlib supplies `NNReal.agmSequences` and `NNReal.agm` ([source](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/ArithmeticGeometricMean.lean#L56)); its sequence index and component ordering differ from the displayed a₀,g₀ convention. The direct DLMF sequences are `DLMF.EllipticIntegrals.agmSeqA`, `DLMF.EllipticIntegrals.agmSeqG`, `DLMF.EllipticIntegrals.agmSeqC` ([source](DLMF/EllipticIntegrals/Quadratic.lean#L41)), with cₙ=√(aₙ²−gₙ²). Other existing real iterations are `DLMF.EllipticIntegrals.agmA`, `DLMF.EllipticIntegrals.agmG` ([source](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L243)), and lean-codes' `Carlson.agmStep`, `Carlson.agmSeq`, `Carlson.agmX`, `Carlson.agmY` ([source](../lean-codes/Carlson/Elliptic/AGMSecondKind.lean#L45)). The independent integral construction `DLMF.Elliptic.agmIntegral` ([source](DLMF/Elliptic/AGM.lean#L122)) is linked to the mean by representation theorems; it is an integral, rather than another name for the limit.

  [DLMF 19.8.E1](https://dlmf.nist.gov/19.8.E1): DLMF's arithmetic means `aₙ` (19.8.1): `a₀`, `a_{n+1} = (aₙ + gₙ)/2`.
  [`DLMF.EllipticIntegrals.agmSeqA`](DLMF/EllipticIntegrals/Quadratic.lean#L41).

  [DLMF 19.8.E1](https://dlmf.nist.gov/19.8.E1): DLMF's geometric means `gₙ` (19.8.1): `g₀`, `g_{n+1} = √(aₙ gₙ)`.
  [`DLMF.EllipticIntegrals.agmSeqG`](DLMF/EllipticIntegrals/Quadratic.lean#L47).

  [DLMF 19.8.E2](https://dlmf.nist.gov/19.8.E2): DLMF 19.8.2: `cₙ = √(aₙ² - gₙ²)`.
  [`DLMF.EllipticIntegrals.agmSeqC`](DLMF/EllipticIntegrals/Quadratic.lean#L53).

- **AGM third-kind correction sequences ε and Q**, [DLMF 19.8.E8](https://dlmf.nist.gov/19.8.E8): `εₙ = (pₙ² - aₙgₙ)/(pₙ² + aₙgₙ)` (DLMF 19.8.8).
  [`DLMF.EllipticIntegrals.agmPiEps`](DLMF/EllipticIntegrals/Quadratic.lean#L298).

  [DLMF 19.8.E8](https://dlmf.nist.gov/19.8.E8): The sequences `(pₙ, εₙ, Qₙ)` of DLMF 19.8.8 with `a₀ = 1`, `g₀`, initial `p₀`, `Q₀ = 1`: `p_{n+1} = (pₙ² + aₙgₙ)/(2pₙ)`, `εₙ = (pₙ² - aₙgₙ)/(pₙ² + aₙgₙ)`, `Q_{n+1} = Qₙεₙ/2` (returned as `(pₙ, Qₙ)`; `εₙ` is `agmPiEps`).
  [`DLMF.EllipticIntegrals.agmPiSeq`](DLMF/EllipticIntegrals/Quadratic.lean#L286).

### §19.9 Inequalities

- **Ellipse perimeter and eccentricity parameter**, [DLMF 19.9.i](https://dlmf.nist.gov/19.9.i):
  L(a,b) is `DLMF.EllipticIntegrals.ellipsePerimeter` ([source](DLMF/EllipticIntegrals/Inequalities.lean#L190)), defined by the arc-length integral. The λ=(a−b)/(a+b) of 19.9.10 and the auxiliary bounds L,U,σ of 19.9.18–22 are expressions in the inequalities, without additional named function definitions. The Ramanujan perimeter formula is an approximation expression, not an alternative exact definition of perimeter.

  [DLMF 19.9.i](https://dlmf.nist.gov/19.9.i): The perimeter `L(a, b)` of an ellipse with semiaxes `a, b` (DLMF §19.9(i)): the arc length `∫₀^{2π} √(a² sin²t + b² cos²t) dt` of `t ↦ (a cos t, b sin t)`.
  [`DLMF.EllipticIntegrals.ellipsePerimeter`](DLMF/EllipticIntegrals/Inequalities.lean#L190).

### §19.11 Addition Theorems

- **Addition-angle sine and cosine**, [DLMF 19.11.E4](https://dlmf.nist.gov/19.11.E4):
  Besides Δ, the right sides specifying sin ψ and cos ψ are `DLMF.EllipticIntegrals.ei19b_addSin`, `DLMF.EllipticIntegrals.ei19b_addCos` ([source](DLMF/EllipticIntegrals/Addition.lean#L53)); their duplication specializations are `DLMF.EllipticIntegrals.ei19b_dupSin`, `DLMF.EllipticIntegrals.ei19b_dupCos` ([source](DLMF/EllipticIntegrals/Addition.lean#L488)). The selected angle and the γ,δ parameters remain quantified/local expressions; these sine/cosine functions alone do not choose a global inverse-sine branch.

### §19.12 Asymptotic Approximations

- **Logarithmic complete-elliptic expansion coefficients**, [DLMF 19.12.E3](https://dlmf.nist.gov/19.12.E3): DLMF 19.12.3: `d(m) = ψ(1 + m) - ψ(½ + m)`, `ψ` the digamma function (`Complex.digamma`).
  [`DLMF.EllipticIntegrals.compEllIntLogCoeff`](DLMF/EllipticIntegrals/Asymptotics.lean#L42).

### §19.14 Reduction of General Elliptic Integrals

- **Legendre reduction auxiliary U**, [DLMF 19.14.E6](https://dlmf.nist.gov/19.14.E6):
  The explicit root expression is `DLMF.EllipticIntegrals.ei19b_redU`, with its admissibility package `DLMF.EllipticIntegrals.ei19b_RedHyp` ([source](DLMF/EllipticIntegrals/Reduction.lean#L136)). The later `DLMF.EllipticIntegrals.ellRedQuadU` of §19.29 gives another actual formulation of this biquadratic reduction parameter.

### §19.16 Definitions

- **Admissible symmetric-integral arguments and cut-root convention**, [DLMF 19.16.i](https://dlmf.nist.gov/19.16.i): DLMF §19.16(i): an admissible argument of a symmetric integral, `x ∈ ℂ \ (-∞, 0]` or `x = 0` (that is, `x` is not a negative real number).
  [`DLMF.EllipticIntegrals.symEllIntArg`](DLMF/EllipticIntegrals/Symmetric.lean#L72).

  [DLMF 19.16.i](https://dlmf.nist.gov/19.16.i): DLMF §19.16(i): the domain of `R_F(x, y, z)` and of the first three arguments of `R_J`: admissible arguments, at most one of them zero.
  [`DLMF.EllipticIntegrals.symEllIntRFDomain`](DLMF/EllipticIntegrals/Symmetric.lean#L77).

<!-- retained entry 144 -->
- **RF, RJ, RG, RD and kernel s(t)**, [19.16.1–5](https://dlmf.nist.gov/19.16.E1):
  `DLMF.EllipticIntegrals.symEllIntRF`, `symEllIntRJ`, `symEllIntRG`,
  `symEllIntRD`, `symEllIntS` in
  [Symmetric](DLMF/EllipticIntegrals/Symmetric.lean#L97).
  These are normalized integrals; RD is an alias specialization of RJ.
  RJ has an explicit principal-value branch for negative real p. Independent
  continued R-function realizations are `Carlson.carlsonRF` in
  [RF](../lean-codes/Carlson/Elliptic/RF.lean#L47) and `Carlson.carlsonRG`
  in [Standard](../lean-codes/Carlson/Elliptic/Standard.lean#L58).

<!-- retained entry 145 -->
- **Five-root hyperelliptic integral**, [19.16.7](https://dlmf.nist.gov/19.16.E7):
  no specifically named five-root function found; it is expressible as a
  specialization of the general R integral.

<!-- retained entry 146 -->
- **Multivariate R-minus-a and conjugate parameter a-prime**,
  [19.16.8–10](https://dlmf.nist.gov/19.16.E8):
  `DLMF.EllipticIntegrals.symEllIntR`, `symEllIntRConj` in
  [Symmetric](DLMF/EllipticIntegrals/Symmetric.lean#L141).
  `symEllIntR a` means Carlson's exponent `-a` and takes boundary limits
  when nodes leave the open product slit plane. lean-codes provides
  `Carlson.carlsonR`, `regCarlsonR` in
  [Explicit](../lean-codes/Carlson/R/Explicit.lean#L322), native simplex/Dirichlet
  integrals `carlsonRIntegral`, `regCarlsonRIntegral` in
  [Basic](../lean-codes/Carlson/R/Basic.lean#L46),
  `carlsonRPositiveRayIntegral` in
  [PositiveRay](../lean-codes/Carlson/R/SingleIntegral/PositiveRay.lean#L45),
  and `carlsonRUnitIntervalIntegral` in
  [Series](../lean-codes/Carlson/R/SingleIntegral/Series.lean#L50).
  The last two are unnormalized integrals; beta factors and the exponent
  transformation identify them with the R-function on their convergence domains.
  Complete symmetric integrals (§19.16(iii)) are zero-node specializations,
  not additional local function definitions.

- **Conjugate exponent and normalized weights**, [DLMF 19.16.E10](https://dlmf.nist.gov/19.16.E10):
  a′=−a+Σbⱼ is `DLMF.EllipticIntegrals.symEllIntRConj` ([source](DLMF/EllipticIntegrals/Symmetric.lean#L239)). In §19.18.3, wⱼ=bⱼ/Σbᵢ and the coordinate vectors eⱼ are local expressions (`Pi.single` for a coordinate vector). Euler–Poisson–Darboux, wave and Laplace specializations in §19.18 are equations/theorem predicates on R and its substitutions, without independently selected solution functions.

### §19.19 Taylor and Related Series

- **Homogeneous symmetric-integral hypergeometric polynomial T**, [DLMF 19.19.E1](https://dlmf.nist.gov/19.19.E1): DLMF 19.19.1: the homogeneous hypergeometric polynomial `T_N(𝐛, 𝐳) = ∑_{m₁+⋯+mₙ = N} ∏ⱼ (bⱼ)_{mⱼ} zⱼ^{mⱼ} / mⱼ!`.
  [`DLMF.EllipticIntegrals.symEllIntT`](DLMF/EllipticIntegrals/SymmetricSeries.lean#L37).

- **Elementary symmetric polynomials and centered variables**, [DLMF 19.19.E4](https://dlmf.nist.gov/19.19.E4):
  Eₛ is `DLMF.EllipticIntegrals.symEllIntE` ([source](DLMF/EllipticIntegrals/SymmetricSeries.lean#L63)), the finite subset-product sum. It accompanies `DLMF.EllipticIntegrals.symEllIntT` (19.19.1). The mean A=(Σzⱼ)/n and centered Zⱼ=1−zⱼ/A of 19.19.6–7 are expressions in the series theorems, not separately named definitions.

### §19.20 Special Cases

- **Lemniscate constants and circular/hyperbolic cases**, [DLMF 19.20.i](https://dlmf.nist.gov/19.20.i):
  The first and second lemniscate constants are the exact expressions R_F(0,1,2) and R_D(0,2,1)/3, also expressed by Γ(1/4),Γ(3/4). No independently named local constants were found. The circular/hyperbolic classification of R_J in §19.20(iii) uses the sign of (p−x)(p−y)(p−z); no separate local classification predicate was found. Decimal evaluations in this section are excluded: numerical.

### §19.22 Quadratic Transformations

- **Bartky/AGM third-kind and second-kind auxiliaries**, [DLMF 19.22.E5](https://dlmf.nist.gov/19.22.E5):
  The transformed p± are `DLMF.EllipticIntegrals.symEllIntPm` ([source](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L155)). The real AGM arithmetic/geometric sequences are `DLMF.EllipticIntegrals.agmA`, `DLMF.EllipticIntegrals.agmG`; the Qₙ for R_D in 19.22.11 is `DLMF.EllipticIntegrals.agmQ` ([source](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L362)). For R_J, 19.22.13 uses the distinct `DLMF.EllipticIntegrals.agmP`, `DLMF.EllipticIntegrals.agmQJ` ([source](DLMF/EllipticIntegrals/SymmetricQuadratic.lean#L581)). They must not be confused with `DLMF.EllipticIntegrals.agmPiSeq` and `DLMF.EllipticIntegrals.agmPiEps` from §19.8.8. The v± and specializations z± in the transformations are expressions, with the displayed sign/positivity restrictions.

### §19.23 Integral Representations

- **Sphere differential form and direction cosines**, [DLMF 19.23.E6](https://dlmf.nist.gov/19.23.E6):
  The spherical integration form and its direction-cosine substitution are `DLMF.EllipticIntegrals.ei19d_sphereForm`, `DLMF.EllipticIntegrals.ei19d_directionCosines` ([source](DLMF/EllipticIntegrals/SymmetricIntegrals.lean#L106)). The simplex and spherical integral formulas for R are representation theorems for the existing R-function, with their branch and measure hypotheses.

### §19.25 Relations to Other Functions

- **Jacobi quotient square-difference constants**, [DLMF 19.25.E28](https://dlmf.nist.gov/19.25.E28): DLMF 19.25.28: `Δ(p, q) = ps²(u, k) - qs²(u, k)` for `p, q ∈ {c, d, n}` (real `u`, parameter `m = k²`), with `Δ(p, q) = -Δ(q, p)`.
  [`DLMF.EllipticIntegrals.jacobiDeltam`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L621).

- **Shifted Weierstrass sigma functions σⱼ**, [DLMF 19.25.E41](https://dlmf.nist.gov/19.25.E41): DLMF 19.25.41: `σ_j(z) = exp(-η_j z) σ(z + ω_j)/σ(ω_j)`, `j = 1, 2, 3`, with `η_j = ζ(ω_j)` (23.2.12) and `ω₂ = -ω₁ - ω₃`.
  [`DLMF.EllipticIntegrals.weierstrassSigmaIdx`](DLMF/EllipticIntegrals/SymmetricRelations.lean#L861).

### §19.26 Addition Theorems

- **Symmetric duplication parameter λ**, [DLMF 19.26.E19](https://dlmf.nist.gov/19.26.E19): DLMF 19.26.19: `λ = √x √y + √y √z + √z √x` (principal square roots).
  [`DLMF.EllipticIntegrals.symEllIntDupLambda`](DLMF/EllipticIntegrals/SymmetricAddition.lean#L505).

### §19.27 Asymptotic Approximations and Expansions

- **Symmetric-integral asymptotic averages and scales**, [DLMF 19.27.E1](https://dlmf.nist.gov/19.27.E1): DLMF 19.27.1: `a = (x + y)/2`.
  [`DLMF.EllipticIntegrals.ellAsymA`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L73).

  [DLMF 19.27.E1](https://dlmf.nist.gov/19.27.E1): DLMF 19.27.1: `b = (y + z)/2`.
  [`DLMF.EllipticIntegrals.ellAsymB`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L77).

  [DLMF 19.27.E1](https://dlmf.nist.gov/19.27.E1): DLMF 19.27.1: `c = (x + y + z)/3`.
  [`DLMF.EllipticIntegrals.ellAsymC`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L81).

  [DLMF 19.27.E1](https://dlmf.nist.gov/19.27.E1): DLMF 19.27.1: `f = (xyz)^{1/3}`.
  [`DLMF.EllipticIntegrals.ellAsymF`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L85).

  [DLMF 19.27.E1](https://dlmf.nist.gov/19.27.E1): DLMF 19.27.1: `g = (xy)^{1/2}`.
  [`DLMF.EllipticIntegrals.ellAsymG`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L89).

  [DLMF 19.27.E1](https://dlmf.nist.gov/19.27.E1): DLMF 19.27.1: `h = (yz)^{1/2}`.
  [`DLMF.EllipticIntegrals.ellAsymH`](DLMF/EllipticIntegrals/SymmetricAsymptotics.lean#L93).

### §19.29 Reduction of General Elliptic Integrals

- **Reduction radicals, determinants, integrands and basic classes**, [DLMF 19.29](https://dlmf.nist.gov/19.29):
  The individual construction entries below include `DLMF.EllipticIntegrals.ellRedRoot`, `DLMF.EllipticIntegrals.ellRedDet`, `DLMF.EllipticIntegrals.ellRedS`, `DLMF.EllipticIntegrals.ellRedU`, its two infinite-endpoint variants, `DLMF.EllipticIntegrals.ellRedU5Sq`, `DLMF.EllipticIntegrals.ellRedS5`, `DLMF.EllipticIntegrals.ellRedQ5Sq`, `DLMF.EllipticIntegrals.ellRedI`, `DLMF.EllipticIntegrals.ellRedE`, `DLMF.EllipticIntegrals.ellRedBasic`, `DLMF.EllipticIntegrals.ellRedS3`, `DLMF.EllipticIntegrals.ellRedQuadU`, `DLMF.EllipticIntegrals.ellRedQuadS`, `DLMF.EllipticIntegrals.ellRedQuadD`, `DLMF.EllipticIntegrals.ellRedQuadRF`, and `DLMF.EllipticIntegrals.ellRedBiquadU`. Their shared namespace is `DLMF.EllipticIntegrals` and [source](DLMF/EllipticIntegrals/SymmetricReduction.lean#L64). There is also `DLMF.EllipticIntegrals.ellRedIntegrand` ([source](DLMF/EllipticIntegrals/SymmetricReduction.lean#L420)) and domain/permutation predicates `DLMF.EllipticIntegrals.EllRedHyp`, `DLMF.EllipticIntegrals.EllRedPerm` ([source](DLMF/EllipticIntegrals/SymmetricReduction.lean#L123)). Only the squares of U_{α5} and Q_{α5} are chosen locally; the DLMF signed roots are not independently supplied. The first-/second-/third-kind classification and the quadratic examples' ξ,η are prose/local formulas, rather than additional selected functions.

  [DLMF 19.29.E1](https://dlmf.nist.gov/19.29.E1): DLMF 19.29.1: `X_α = √(a_α + b_α x)` (and `Y_α = √(a_α + b_α y)` is `ellRedRoot a b y α`), principal square root.
  [`DLMF.EllipticIntegrals.ellRedRoot`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L64).

  [DLMF 19.29.E2](https://dlmf.nist.gov/19.29.E2): DLMF 19.29.2: `d_{αβ} = a_α b_β - a_β b_α`.
  [`DLMF.EllipticIntegrals.ellRedDet`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L69).

  [DLMF 19.29.E3](https://dlmf.nist.gov/19.29.E3): DLMF 19.29.3: `s(t) = ∏_{α=1}^{4} √(a_α + b_α t)` (Lean indices `0, …, 3`). Cubic cases are obtained by setting one factor equal to `1` (`a = 1`, `b = 0`).
  [`DLMF.EllipticIntegrals.ellRedS`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L73).

  [DLMF 19.29.E5](https://dlmf.nist.gov/19.29.E5): DLMF 19.29.5: `U_{αβ} = (X_α X_β Y_γ Y_δ + Y_α Y_β X_γ X_δ)/(x - y)`, for a permutation `α, β, γ, δ` of the four factors (the complementary pair `γ, δ` is given explicitly).
  [`DLMF.EllipticIntegrals.ellRedU`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L79).

  [DLMF 19.29.E9](https://dlmf.nist.gov/19.29.E9): DLMF 19.29.9: `Q_{α5}² = (X_5 Y_5 / (X_α Y_α))² U_{α5}²` (DLMF defines `Q_{α5} = X_5 Y_5 U_{α5} / (X_α Y_α)`; only its square enters (19.29.8)).
  [`DLMF.EllipticIntegrals.ellRedQ5Sq`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L116).

  [DLMF 19.29.E9](https://dlmf.nist.gov/19.29.E9): DLMF 19.29.9: `S_{α5} = (X_β X_γ X_δ Y_5² / X_α + Y_β Y_γ Y_δ X_5² / Y_α)/(x - y)`.
  [`DLMF.EllipticIntegrals.ellRedS5`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L108).

  [DLMF 19.29.E9](https://dlmf.nist.gov/19.29.E9): DLMF 19.29.9: `U_{α5}² = U_{αβ}² - d_{αγ} d_{αδ} d_{β5} / d_{α5}` (Lean index `4` for DLMF's `5`). Only the square `U_{α5}²` enters (19.29.8).
  [`DLMF.EllipticIntegrals.ellRedU5Sq`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L101).

  [DLMF 19.29.E11](https://dlmf.nist.gov/19.29.E11): DLMF 19.29.11: `I(𝐦) = ∫_y^x ∏_{α=1}^{h} (a_α + b_α t)^{-1/2} ∏_{j=1}^{n} (a_j + b_j t)^{m_j} dt`, `x > y`, `h = 3` or `4`, `n ≥ h`, integer `m_j` (DLMF's rewriting of (19.2.3)).
  [`DLMF.EllipticIntegrals.ellRedI`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L427).

  [DLMF 19.29.E12](https://dlmf.nist.gov/19.29.E12): DLMF 19.29.12: the unit vector `𝐞_j` (`1` in the `j`th position, `0` elsewhere).
  [`DLMF.EllipticIntegrals.ellRedE`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L433).

  [DLMF 19.29.E13](https://dlmf.nist.gov/19.29.E13): DLMF 19.29.13, 19.29.14: the index vectors of the basic integrals: `I(𝟎)`, `I(-𝐞_j)` (`1 ≤ j ≤ n`) and, in the quartic case `h = 4`, also `I(𝐞_α)` (`1 ≤ α ≤ 4`). The integrals of (19.29.4), (19.29.7), (19.29.8) are `I(𝟎)`, `I(𝐞_α - 𝐞_δ)`, `I(𝐞_α - 𝐞_5)` (19.29.ii.p1).
  [`DLMF.EllipticIntegrals.ellRedBasic`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L443).

  [DLMF 19.29.E17](https://dlmf.nist.gov/19.29.E17): DLMF 19.29.17: `s(t) = ∏_{α=1}^{3} √(a_α + b_α t)` (cubic case).
  [`DLMF.EllipticIntegrals.ellRedS3`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L544).

  [DLMF 19.29.E22](https://dlmf.nist.gov/19.29.E22): DLMF 19.29.22: `U` defined by `(x² - y²) U = x √(Q₁(y) Q₂(y)) + y √(Q₁(x) Q₂(x))`, `Q_j(t) = a_j + b_j t²`.
  [`DLMF.EllipticIntegrals.ellRedQuadU`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L692).

  [DLMF 19.29.E24](https://dlmf.nist.gov/19.29.E24): DLMF 19.29.24 with 19.29.25: the right side `4 R_F(U, U + D₁₂ + V, U + D₁₂ - V)` with `(x - y)² U = S₁ S₂` and `V = √(D₁₂² - D₁₁ D₂₂)` (principal complex square root: the variables of `R_F` are real and nonnegative unless both quadratics have real zeros and those of `Q₁` interlace those of `Q₂`, 19.29.iii.p2).
  [`DLMF.EllipticIntegrals.ellRedQuadRF`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L837).

  [DLMF 19.29.E25](https://dlmf.nist.gov/19.29.E25): DLMF 19.29.25: `D_{jl} = 2 f_j h_l + 2 h_j f_l - g_j g_l`.
  [`DLMF.EllipticIntegrals.ellRedQuadD`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L833).

  [DLMF 19.29.E25](https://dlmf.nist.gov/19.29.E25): DLMF 19.29.25: `S_j = (√Q_j(x) + √Q_j(y))² - h_j (x - y)²` for `Q_j(t) = f_j + g_j t + h_j t²`.
  [`DLMF.EllipticIntegrals.ellRedQuadS`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L827).

  [DLMF 19.29.E31](https://dlmf.nist.gov/19.29.E31): DLMF 19.29.31: `(x - y)² U = (√Q(x²) + √Q(y²))² - h (x² - y²)²`, `Q(s) = f + g s + h s²`.
  [`DLMF.EllipticIntegrals.ellRedBiquadU`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L959).

- **Infinite-endpoint symmetric-reduction variables**, [DLMF 19.29.E6](https://dlmf.nist.gov/19.29.E6): DLMF 19.29.6, case `x = ∞`: `U_{αβ} = √b_α √b_β Y_γ Y_δ + Y_α Y_β √b_γ √b_δ`.
  [`DLMF.EllipticIntegrals.ellRedUInf`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L87).

  [DLMF 19.29.E6](https://dlmf.nist.gov/19.29.E6): DLMF 19.29.6, case `y = -∞`: `U_{αβ} = X_α X_β √(-b_γ) √(-b_δ) + √(-b_α) √(-b_β) X_γ X_δ`.
  [`DLMF.EllipticIntegrals.ellRedUNegInf`](DLMF/EllipticIntegrals/SymmetricReduction.lean#L94).

### §19.30 Lengths of Plane Curves

- **Plane curves and their arc lengths**, [DLMF 19.30](https://dlmf.nist.gov/19.30):
  Ellipses, hyperbolas and Bernoulli's lemniscate are given by the explicit parametrizations of 19.30.1, .7, .10, with arc lengths s in .2, .8, .11. The full ellipse perimeter has both `DLMF.EllipticIntegrals.ellipsePerimeter` and the older `DLMF.Elliptic.ellipsePerimeter` ([source](DLMF/Elliptic/SpecialValues.lean#L213)); no separate local hyperbola or lemniscate arc-length construction was found. The scale parameters k,c,r,q and the amplitude in .12 are formula substitutions. Exact lemniscate perimeter expressions remain definitions/identities of interest; their decimal evaluations are excluded: numerical.

### §19.31 Probability Distributions

- **Quadratic-form Gaussian averages and rectangle map**, [DLMF 19.31.E1](https://dlmf.nist.gov/19.31.E1):
  xᵀAx is `dotProduct`/matrix multiplication expressed as the finite double sum; the weighted Gaussian integral in 19.31.2 uses the existing R-function, without a new named distribution. The map z(p)=R_F(p−x₁,p−x₂,p−x₃) in [19.32.1](https://dlmf.nist.gov/19.32.E1) is an explicit substitution in R_F; no separate local named rectangle map was found. Its upper-half-plane and ordered-real-root restrictions determine the relevant branches.

### §19.33 Triaxial Ellipsoids

- **Ellipsoid surface, potential, capacity, depolarization and self-energy**, [DLMF 19.33](https://dlmf.nist.gov/19.33):
  The named quantities S,V(λ),C,L_a,L_b,L_c,U and density profile ρ are defined in 19.33.1–12 using the given semiaxes and charges; g(r)=4π∫ᵣ^∞f(t)t dt is an additional radial auxiliary. They have no independently named construction in this project's elliptic-integral modules. The R_G,R_F,R_D expressions are representations with the given normalization (in particular L_a+L_b+L_c=4π in cgs units), not a change to the Carlson function definitions.

### §19.34 Mutual Inductance of Coaxial Circles

- **Mutual inductance and circle-distance parameters**, [DLMF 19.34.E1](https://dlmf.nist.gov/19.34.E1):
  The integral defines mutual inductance M of coaxial circles, with r±²=h²+(a±b)² and a₃=h²+a²+b². No dedicated local M or distance-parameter construction was found; the Carlson functions used in the exact representations already exist.

### §19.36 Methods of Computation

- **Exact iteration auxiliaries in computation sections**, [DLMF 19.36.E6](https://dlmf.nist.gov/19.36.E6):
  The aₙ,cₙ,tₙ sequences, their limits M,T, and hₙ=√(tₙ²+θaₙ²) in 19.36.6–13 are defined by the stated θ=±1 recurrences and hypotheses. No matching dedicated local iteration was found; these recurrences differ from the two-sequence complete AGM. The degree-seven expressions in 19.36.1–2 are truncations in the already defined Eₛ. They and the tabulated shape parameters σ,γ in §19.37 are recorded descriptively; no numerical evaluation or approximation code is being added. §§19.35,19.38,19.39 introduce no additional function families beyond the cited applications and approximation methods.

## Chapter 20 — Theta functions

Expanded review: all 16 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§20.1–20.16 checked; the matching section is §20.2.

### §20.1 Special Notation

- **Nome, nome powers and alternate theta normalizations**, [DLMF 20.1](https://dlmf.nist.gov/20.1):
  q=exp(iπτ), with τ known, and q^α means exp(iαπτ), not an independently chosen principal power of q. The explicit τ-based theta constructions ([source](DLMF/Elliptic/Basic/Theta.lean)) retain this information; no separate nome wrapper is needed. Jacobi's Θ,Θ₁,H,H₁ are the four classical theta functions with u=z/θ₃(0|τ)²; McKean–Moll's ϑⱼ is θⱼ(πz|τ), without independent local wrappers. Neville's θ_s,θ_c,θ_d,θ_n are the four normalized/rescaled formulas in §20.1; `DLMF.JacobiElliptic.jacobiLetterTheta` and `DLMF.JacobiElliptic.jacobiGlaisher` ([source](DLMF/JacobiElliptic/Basic/Definitions.lean#L47)) supply the letter/quotient construction. A quotient cancels some normalizing factors, so these ratio constructions are not separately normalized Neville functions.

### §20.2 Definitions and Periodic Properties

<!-- retained entry 148 -->
- **Theta constants and derivative at zero**, [20.2(i) prose](https://dlmf.nist.gov/20.2.i):
  `DLMF.Theta.jacobiThetaTwoNullTau`, `jacobiThetaThreeNullTau`,
  `jacobiThetaFourNullTau`, `jacobiThetaTwoNullQ`, `jacobiThetaThreeNullQ`,
  `jacobiThetaFourNullQ` are abbreviations
  at z=0; `jacobiThetaOneDerivNullTau`, `jacobiThetaOneDerivNullQ` are
  derivative definitions in [Basic](DLMF/Theta/Basic/Definitions.lean#L40).

<!-- retained entry 147 -->
- **Four Jacobi theta functions**, [20.2.1–4](https://dlmf.nist.gov/20.2.E1):
  `DLMF.Elliptic.jacobiThetaOneTau`, `jacobiThetaTwoTau`,
  `jacobiThetaThreeTau`, `jacobiThetaFourTau` in
  [Theta/Defs](DLMF/Elliptic/Basic/Theta.lean#L26), and independent nome-series
  definitions `DLMF.Theta.jacobiThetaOneQ`, `jacobiThetaTwoQ`,
  `jacobiThetaThreeQ`, `jacobiThetaFourQ` in
  [Basic](DLMF/Theta/Basic/Definitions.lean#L23). Mathlib `jacobiTheta₂` in
  [TwoVariable](.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean)
  is the native two-variable construction underlying theta-three, with
  argument `z/π`; its subscript does not mean DLMF theta-two. The nome is
  `q=exp(πiτ)`. Nome powers in theta-one/two use a principal quarter-power,
  so converting from τ must respect the selected logarithm.

<!-- retained entry 149 -->
- **Lattice points and half-period multiplier M**,
  [20.2.5](https://dlmf.nist.gov/20.2.E5), [20.2.10](https://dlmf.nist.gov/20.2.E10):
  `DLMF.Theta.latticePoint`, `thetaMultiplierM` in
  [Basic](DLMF/Theta/Basic/Definitions.lean#L73). The fundamental parallelogram is a
  region described by its vertices, without another local region definition.

- **Theta lattice points and multiplier**, [DLMF 20.2.E5](https://dlmf.nist.gov/20.2.E5):
  z_{m,n}=(m+nτ)π is `DLMF.Theta.latticePoint`; M(z|τ)=exp(iz+iπτ/4) from 20.2.10 is `DLMF.Theta.thetaMultiplierM` ([source](DLMF/Theta/Basic/Definitions.lean#L73)). They supplement the Fourier-series definitions with the lattice and quasiperiod factors.

### §20.6 Power Series

- **Eisenstein-order theta lattice coefficients and radius**, [DLMF 20.6.E1](https://dlmf.nist.gov/20.6.E1):
  The nearest nonzero lattice-point norm is `DLMF.Theta.thetaLatticeMinNorm`; δ,α,β,γ are the four actual iterated sums `DLMF.Theta.thetaDelta`, `DLMF.Theta.thetaAlpha`, `DLMF.Theta.thetaBeta`, `DLMF.Theta.thetaGamma` ([source](DLMF/Theta/PowerSeries.lean#L33)). At exponent two, summation order matters; ordinary absolute double summation must not be substituted for the Eisenstein convention. These are coefficient constructions for the theta functions, not separate theta normalizations.

  [DLMF 20.6.E1](https://dlmf.nist.gov/20.6.E1): DLMF 20.6.1: the radius `min_{(m,n) ≠ (0,0)} |z_{m,n}| = min |(m + nτ)π|`; the power series 20.6.2–20.6.5 hold for `|πz|` below it.
  [`DLMF.Theta.thetaLatticeMinNorm`](DLMF/Theta/PowerSeries.lean#L55).

  [DLMF 20.6.E6](https://dlmf.nist.gov/20.6.E6): DLMF 20.6.6: `δ_k(τ) = ∑_n ∑'_m (m + nτ)^{-k}` (`(m,n) ≠ (0,0)`; DLMF writes `δ_{2j}`, `k = 2j`). Iterated sum, inner over `m`.
  [`DLMF.Theta.thetaDelta`](DLMF/Theta/PowerSeries.lean#L33).

  [DLMF 20.6.E7](https://dlmf.nist.gov/20.6.E7): DLMF 20.6.7: `α_k(τ) = ∑_n ∑_m (m - 1/2 + nτ)^{-k}` (`k = 2j`).
  [`DLMF.Theta.thetaAlpha`](DLMF/Theta/PowerSeries.lean#L40).

  [DLMF 20.6.E8](https://dlmf.nist.gov/20.6.E8): DLMF 20.6.8: `β_k(τ) = ∑_n ∑_m (m - 1/2 + (n - 1/2)τ)^{-k}` (`k = 2j`).
  [`DLMF.Theta.thetaBeta`](DLMF/Theta/PowerSeries.lean#L45).

  [DLMF 20.6.E9](https://dlmf.nist.gov/20.6.E9): DLMF 20.6.9: `γ_k(τ) = ∑_n ∑_m (m + (n - 1/2)τ)^{-k}` (`k = 2j`).
  [`DLMF.Theta.thetaGamma`](DLMF/Theta/PowerSeries.lean#L50).

### §20.7 Identities

- **Landen normalizing factors**, [DLMF 20.7.E15](https://dlmf.nist.gov/20.7.E15):
  A(τ)=1/θ₄(0|2τ) and B(τ)=1/(θ₃(0|τ)θ₄(0|τ)θ₃(π/4|τ)) are `DLMF.Theta.thetaLandenA`, `DLMF.Theta.thetaLandenB` ([source](DLMF/Theta/Identities.lean#L606)). The transformed τ′=−1/τ in 20.7.30–33 is a formula substitution, using principal square roots.

  [DLMF 20.7.E15](https://dlmf.nist.gov/20.7.E15): DLMF 20.7.15: `A(τ) = 1/θ₄(0|2τ)`.
  [`DLMF.Theta.thetaLandenA`](DLMF/Theta/Identities.lean#L606).

  [DLMF 20.7.E20](https://dlmf.nist.gov/20.7.E20): DLMF 20.7.20: `B(τ) = 1/(θ₃(0|τ) θ₄(0|τ) θ₃(π/4|τ))`.
  [`DLMF.Theta.thetaLandenB`](DLMF/Theta/Identities.lean#L642).

### §20.9 Relations to Other Functions

- **Theta modulus and elliptic modular function**, [DLMF 20.9.E1](https://dlmf.nist.gov/20.9.E1):
  k=θ₂²/θ₃² is both `DLMF.Theta.thetaModulusK` ([source](DLMF/Theta/Relations.lean#L52)) and `DLMF.JacobiElliptic.jacobiModulusTau` ([source](DLMF/JacobiElliptic/Basic/Definitions.lean#L74)); its square is the modular function `DLMF.Weierstrass.modularLambda`. The quarter-period constructions `DLMF.JacobiElliptic.compEllIntKTau`, `DLMF.JacobiElliptic.compEllIntKpTau` give the theta-side K,K′. Their equalities with integral constructions are bridge theorems, and the nome does not determine τ uniquely.

  [DLMF 20.9.E1](https://dlmf.nist.gov/20.9.E1): DLMF 20.9.1: the modulus `k = θ₂²(0|τ)/θ₃²(0|τ)`.
  [`DLMF.Theta.thetaModulusK`](DLMF/Theta/Relations.lean#L52).

### §20.11 Generalizations and Analogs

- **Gauss sums, Ramanujan theta and combined theta functions**, [DLMF 20.11.E1](https://dlmf.nist.gov/20.11.E1):
  Actual constructions are `DLMF.Theta.thetaGaussSum`, `DLMF.Theta.ramanujanThetaF`, and `DLMF.Theta.combinedTheta` ([source](DLMF/Theta/Generalizations.lean#L35)). The finite Gauss sum carries the DLMF coprimality/parity hypotheses in its theorems; the bilateral Ramanujan theta requires |ab|<1. The twelve combined functions of 20.11.6–8 are one indexed construction with different normalizing factors when a letter is 1. Ramanujan's changes of base in §20.11(iii) name hypergeometric inversion identities, without a newly selected function.

  [DLMF 20.11.E1](https://dlmf.nist.gov/20.11.E1): DLMF 20.11.1: the Gauss sum `G(m,n) = ∑_{k=0}^{n-1} e^{-πik²m/n}` (DLMF assumes `m, n` coprime, `n > 0`, `mn` even).
  [`DLMF.Theta.thetaGaussSum`](DLMF/Theta/Generalizations.lean#L35).

  [DLMF 20.11.E3](https://dlmf.nist.gov/20.11.E3): DLMF 20.11.3: Ramanujan's theta function `f(a,b) = ∑_{n∈ℤ} a^{n(n+1)/2} b^{n(n-1)/2}`, `|ab| < 1` (the exponents are integers).
  [`DLMF.Theta.ramanujanThetaF`](DLMF/Theta/Generalizations.lean#L61).

  [DLMF 20.11.E6](https://dlmf.nist.gov/20.11.E6): DLMF 20.11.6–20.11.8: the twelve combined theta functions `φ_{m,n}(z,q) = c_n θ_m(z|τ)/(c_m θ_n(z|τ))` for `m ≠ n` in `{1,2,3,4}`, where `c₁ = θ₁'(0|τ)` and `cⱼ = θⱼ(0|τ)` for `j = 2,3,4`; this single formula is 20.11.6 (`n = 1`), 20.11.7 (`m = 1`) and 20.11.8 (`m, n ≥ 2`).
  [`DLMF.Theta.combinedTheta`](DLMF/Theta/Generalizations.lean#L169).

### §20.12 Mathematical Applications

- **Complex torus and theta embedding**, [DLMF 20.12.ii](https://dlmf.nist.gov/20.12.ii):
  ℂ/(ℤ+τℤ) identifies z₁,z₂ when their difference is m+τn. Mathlib's quotient of an additive subgroup represents this relation; `PeriodPair.lattice` ([source](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean#L79)) supplies a lattice when period-pair data are used; `PeriodPair` is a root-level Mathlib namespace, not the local `DLMF.Weierstrass.HalfPeriods` namespace. The four-coordinate projective map built from θⱼ(2z|τ) has no separate local named construction. It is recorded descriptively as an application, without claiming a formalized projective embedding.

### §20.13 Physical Applications

- **Heat-equation Gaussian and periodization**, [DLMF 20.13.E3](https://dlmf.nist.gov/20.13.E3):
  g(z,t)=√(π/(4αt))exp(−z²/(4αt)) is an explicit Gaussian expression; the periodic and antiperiodic sums in .4–5 are theta representations. No independent local heat-kernel function was found. The modular angle α in [20.15.1](https://dlmf.nist.gov/20.15.E1) is specified by sin α=k, and u,ε in those tables are argument rescalings, without local angle wrappers. Decimal tables and numerical evaluation examples remain excluded: numerical. §§20.3–5,20.8,20.10,20.14,20.16 otherwise add identities, graphs or methods rather than new named function families; the threshold q^Dedekind in the graphics is descriptive and has no selected local maximizer.

## Chapter 21 — Multidimensional theta functions

Expanded review: all 11 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§21.1–21.11 checked; the matching section is §21.2.

### §21.1 Special Notation

- **Riemann matrices, symplectic sign convention and alternate theta normalization**, [DLMF 21.1](https://dlmf.nist.gov/21.1):
  `DLMF.RiemannTheta.siegelUpperHalfSpace` is the set of symmetric complex matrices with positive-definite imaginary part ([source](DLMF/RiemannTheta/Basic/Definitions.lean#L29)). Θ(φ|B)=θ(φ/(2πi)|B/(2πi)) is `DLMF.RiemannTheta.riemannThetaBig`. The block matrix J_{2g}=[[0,I],[-I,0]] is `DLMF.RiemannTheta.symplecticJ` ([source](DLMF/RiemannTheta/Modular.lean#L56)); it is the negative of Mathlib's `Matrix.J`. Vectors and integer matrices are finite function/matrix types, and diag A is `Matrix.diag`. The oriented intersection index on surface cycles has no corresponding local surface-cycle construction.

  [DLMF 21.1](https://dlmf.nist.gov/21.1): DLMF's `J_{2g} = [[0, I], [-I, 0]]` (DLMF §21.1). It is `-Matrix.J` in Mathlib.
  [`DLMF.RiemannTheta.symplecticJ`](DLMF/RiemannTheta/Modular.lean#L56).

### §21.2 Definitions

<!-- retained entry 150 -->
- **Riemann theta**, [21.2.1](https://dlmf.nist.gov/21.2.E1):
  `DLMF.RiemannTheta.riemannTheta` and its summand `riemannThetaTerm` in
  [Basic](DLMF/RiemannTheta/Basic/Definitions.lean#L35), with an arbitrary finite index
  type for genus. `siegelUpperHalfSpace` is the symmetric positive-imaginary-part
  matrix domain from §21.1. `riemannThetaBig` is the alternative normalization
  `Θ(φ|B)=θ(φ/(2πi)|B/(2πi))`, not an independent continuation.

<!-- retained entry 151 -->
- **Scaled Riemann theta**, [21.2.2](https://dlmf.nist.gov/21.2.E2):
  `DLMF.RiemannTheta.riemannThetaScaled` in
  [Basic](DLMF/RiemannTheta/Basic/Definitions.lean#L58). This is an exact nonanalytic
  rescaling, not a numerical approximation, so it belongs in the inventory.

- **Explicit genus-two Riemann matrix**, [DLMF 21.2.E3](https://dlmf.nist.gov/21.2.E3): The Riemann matrix `[[i, -1/2], [-1/2, i]]` of DLMF 21.2.3 (also `Ω₁` of 21.4.2).
  [`DLMF.RiemannTheta.riemannMatrixExample`](DLMF/RiemannTheta/Basic/Definitions.lean#L75).

<!-- retained entry 152 -->
- **Theta with characteristics and half-period characteristics**,
  [21.2.5 and adjacent prose](https://dlmf.nist.gov/21.2.E5):
  `DLMF.RiemannTheta.riemannThetaChar`, `riemannThetaCharTerm`, and
  `halfPeriodCharacteristics` in [Basic](DLMF/RiemannTheta/Basic/Definitions.lean#L46).
  The characteristic vectors are real; the final set restricts each entry
  to 0 or 1/2. The translated-theta formula 21.2.6 is a bridge.

### §21.3 Symmetry and Quasi-Periodicity

- **Period lattice of a Riemann theta function**, [DLMF 21.3.i](https://dlmf.nist.gov/21.3.i):
  {m₁+Ωm₂ : m₁,m₂∈ℤᵍ} is `DLMF.RiemannTheta.riemannThetaPeriodLattice` ([source](DLMF/RiemannTheta/Symmetry.lean#L107)). The theta function is quasi-periodic along this lattice; this does not assert ordinary periodicity for the Ωm₂ directions.

  [DLMF 21.3.i](https://dlmf.nist.gov/21.3.i): The period lattice `{m₁ + Ωm₂ : m₁, m₂ ∈ ℤ^g}` of the Riemann theta function (DLMF §21.3(i)).
  [`DLMF.RiemannTheta.riemannThetaPeriodLattice`](DLMF/RiemannTheta/Symmetry.lean#L107).

### §21.4 Graphics

- **Exact example Riemann matrices**, [DLMF 21.4.E2](https://dlmf.nist.gov/21.4.E2):
  Ω₁ is the existing `DLMF.RiemannTheta.riemannMatrixExample` of 21.2.3; Ω₂ is `DLMF.RiemannTheta.riemannMatrixOmegaTwo` ([source](DLMF/RiemannTheta/Basic/Definitions.lean#L79)). They are exact matrix constructions even though repeated in a graphics section. The decimal matrix in 21.4.1 and graphs are excluded: numerical/graphical.

  [DLMF 21.4.E3](https://dlmf.nist.gov/21.4.E3): The `3 × 3` Riemann matrix `Ω₂` of DLMF 21.4.3 (graphics section; exact matrix retained).
  [`DLMF.RiemannTheta.riemannMatrixOmegaTwo`](DLMF/RiemannTheta/Basic/Definitions.lean#L79).

### §21.5 Modular Transformations

- **Symplectic modular transformations and multipliers**, [DLMF 21.5.E1](https://dlmf.nist.gov/21.5.E1):
  `DLMF.RiemannTheta.IsSymplectic` and `DLMF.RiemannTheta.IsSymplecticBlocks` ([source](DLMF/RiemannTheta/Modular.lean#L62)) express ΓJΓᵀ=J for the whole matrix or its integer blocks. The transformed z,Ω and transformed characteristics are formula expressions. ξ(Γ), an eighth root of unity, and κ(α,β,Γ) are existential constants in transformation statements, without selected global multiplier definitions.

  [DLMF 21.5.E1](https://dlmf.nist.gov/21.5.E1): The block matrix `Γ = [[A, B], [C, D]]` of integer `g × g` matrices is symplectic (DLMF 21.5.1–21.5.2).
  [`DLMF.RiemannTheta.IsSymplecticBlocks`](DLMF/RiemannTheta/Modular.lean#L67).

  [DLMF 21.5.E2](https://dlmf.nist.gov/21.5.E2): The symplectic condition `Γ J_{2g} Γᵀ = J_{2g}` (DLMF 21.5.2).
  [`DLMF.RiemannTheta.IsSymplectic`](DLMF/RiemannTheta/Modular.lean#L62).

### §21.6 Products

- **Riemann product quotients and representatives**, [DLMF 21.6.E1](https://dlmf.nist.gov/21.6.E1):
  Besides `DLMF.RiemannTheta.riemannK` and `DLMF.RiemannTheta.riemannD`, the actual underlying constructions are `DLMF.RiemannTheta.riemannKSet`, `DLMF.RiemannTheta.riemannKSetoid`, `DLMF.RiemannTheta.riemannDSet`, `DLMF.RiemannTheta.riemannDSetoid`, and `DLMF.RiemannTheta.IsRiemannKRepresentatives` ([source](DLMF/RiemannTheta/Products.lean#L51)). K is a quotient type, D a `Nat.card`, not a numerical approximation. The rational orthogonal example matrix is `DLMF.RiemannTheta.riemannTExample`; the finite half-characteristic encoding is `DLMF.RiemannTheta.rth21_half` and the sums use `Fin 2` vectors. These are explicit representatives of the DLMF quotient rather than distinct theta function families.

  [DLMF 21.6.E1](https://dlmf.nist.gov/21.6.E1): `𝒦 = ℤ^{g×h}T / (ℤ^{g×h}T ∩ ℤ^{g×h})` (DLMF 21.6.1).
  [`DLMF.RiemannTheta.riemannK`](DLMF/RiemannTheta/Products.lean#L61).

  [DLMF 21.6.E2](https://dlmf.nist.gov/21.6.E2): `𝒟 = |Tᵀ ℤ^h / (Tᵀ ℤ^h ∩ ℤ^h)|` (DLMF 21.6.2); `Nat.card` of the quotient.
  [`DLMF.RiemannTheta.riemannD`](DLMF/RiemannTheta/Products.lean#L77).

  [DLMF 21.6.E5](https://dlmf.nist.gov/21.6.E5): The rational orthogonal matrix `T = ½[[1,1,1,1],[1,1,-1,-1],[1,-1,1,-1],[1,-1,-1,1]]` (DLMF 21.6.5).
  [`DLMF.RiemannTheta.riemannTExample`](DLMF/RiemannTheta/Products.lean#L132).

### §21.7 Riemann Surfaces

- **Plane curves, compact Riemann surfaces, genus, cycles and period matrix**, [DLMF 21.7.E1](https://dlmf.nist.gov/21.7.E1):
  DLMF constructs a compact Riemann surface by projectivizing an irreducible plane curve and removing its singularities. It specifies genus g, a symplectic cycle basis aⱼ,bⱼ, normalized holomorphic differentials ωⱼ, and Ωⱼₖ=∮bₖωⱼ (21.7.2–6). The project has no corresponding local surface, normalization or period-map construction; `DLMF.RiemannTheta.siegelUpperHalfSpace` records the target matrix condition only.

- **Theta differential and prime form**, [DLMF 21.7.E8](https://dlmf.nist.gov/21.7.E8):
  ζ=Σωⱼ∂ⱼ`θ[α;β](0|Ω)`, with the nonzero-gradient condition of .7, and E(P₁,P₂)=`θ[α;β](∫P₁^P₂ω|Ω)`/(√ζ(P₁)√ζ(P₂)) are not defined locally. The square-root choices and common integration paths are part of this definition; arbitrary pointwise principal square roots are insufficient.

- **Hyperelliptic surface and branch characteristics**, [DLMF 21.7.E11](https://dlmf.nist.gov/21.7.E11):
  μ²=Q(λ), degree Q=2g+1≥5, determines the hyperelliptic surface, branch-point set B (including infinity), chosen subset U, and characteristic map η on even subsets, with components η¹,η². The symmetric difference T₁⊖T₂ in .12 is Mathlib `symmDiff`; the surface-dependent η and branch-point construction are absent locally. Equations .13–16 are compatibility properties, not arbitrary formulas choosing η.

### §21.8 Abelian Functions

- **Abelian functions and integrable equations**, [DLMF 21.8](https://dlmf.nist.gov/21.8):
  An Abelian function is meromorphic in g complex variables and periodic with respect to a 2g-period lattice. No dedicated local predicate was found. §21.9 defines the KdV, nonlinear Schrödinger and KP equations and the theta expression u=c+2∂ₓ²log θ(kx+ly+ωt+φ|Ω); these equation predicates/solution constructions are not provided locally. The Schottky problem asks which Riemann matrices arise from compact Riemann surfaces. These application definitions are recorded descriptively. §§21.10–11 add method/software references only.

## Chapter 22 — Jacobian elliptic functions

Expanded review: all 22 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§22.1–22.22 checked; matching headings are §22.2,
§22.15(i), and the “Definition” paragraphs in §22.16(i)/(iii).

### §22.2 Definitions

<!-- retained entry 153 -->
- **Nome, modulus, complementary modulus, K and scaled argument ζ**,
  [22.2.1–3](https://dlmf.nist.gov/22.2.E1):
  `DLMF.JacobiElliptic.jacobiNomek`, `jacobiTauk`, `jacobiComodulusk`,
  `jacobiZetak`, `compEllIntKk`, `compEllIntKpk`, and the τ-based
  `jacobiModulusTau`, `jacobiComodulusTau`, `compEllIntKTau`,
  `compEllIntKpTau`, `jacobiZetaTau` in
  [Definitions](DLMF/JacobiElliptic/Basic/Definitions.lean#L65).
  Here “Zeta” denotes the scaled argument πz/(2K), not Jacobi's zeta function.

<!-- retained entry 154 -->
- **All twelve Jacobi functions and Glaisher quotients**,
  [22.2.4–12](https://dlmf.nist.gov/22.2.E4):
  `DLMF.JacobiElliptic.jacobiGlaisher`, `jacobiPQTau`, `jacobiPQk`, with
  `JacobiLetter`, in [Definitions](DLMF/JacobiElliptic/Basic/Definitions.lean#L58).
  The explicit modulus-k wrappers are `jacobiSnk`, `jacobiCnk`, `jacobiDnk`,
  `jacobiSdk`, `jacobiCdk`, `jacobiSck`, `jacobiNsk`, `jacobiNck`,
  `jacobiNdk`, `jacobiDsk`, `jacobiDck`, `jacobiCsk`; each has a corresponding
  τ wrapper `jacobiSnTau`, …, `jacobiCsTau` in the same file.
  Independent real inverse-integral constructions are
  `DLMF.Elliptic.Real.jacobiSnm`, `jacobiCnm`, `jacobiDnm` in
  [Jacobi](DLMF/Elliptic/Basic/Amplitude.lean#L144), with parameter `m=k²`.
  Their amplitude definition uses a fallback when `m ≥ 1`; it is not a
  general mathematical extension to that regime.

### §22.4 Periods, Poles, and Zeros

- **Jacobian congruence classes and letter vertices**, [DLMF 22.4.i](https://dlmf.nist.gov/22.4.i):
  The congruent set of a is {a+2mK+2niK′}. It is `DLMF.JacobiElliptic.jacobiCongruentk`; the vertices s=0,c=K,d=K+iK′,n=iK′ are `DLMF.JacobiElliptic.jacobiLetterPointk` ([source](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L865)). Copolar means having the same pole column and coperiodic the same period row in Tables22.4.1–2; no independent local predicates were found. The geometric lattice generated by K,iK′ differs from each function's actual period lattice.

### §22.7 Landen Transformations

- **Descending Landen modulus**, [DLMF 22.7.E1](https://dlmf.nist.gov/22.7.E1): The descending Landen modulus `k₁ = (1 - k')/(1 + k')` (DLMF 22.7.1).
  [`DLMF.JacobiElliptic.jacobiLandenDescModulus`](DLMF/JacobiElliptic/Landen.lean#L30).

- **Ascending Landen modulus and complementary modulus**, [DLMF 22.7.E5](https://dlmf.nist.gov/22.7.E5): The ascending complementary Landen modulus `k₂' = (1 - k)/(1 + k)` (DLMF 22.7.5).
  [`DLMF.JacobiElliptic.jacobiLandenAscComodulus`](DLMF/JacobiElliptic/Landen.lean#L38).

  [DLMF 22.7.E5](https://dlmf.nist.gov/22.7.E5): The ascending Landen modulus `k₂ = 2√k/(1 + k)` (DLMF 22.7.5, principal square root).
  [`DLMF.JacobiElliptic.jacobiLandenAscModulus`](DLMF/JacobiElliptic/Landen.lean#L34).

### §22.9 Cyclic Identities

- **Cyclic sample values and identity rank**, [DLMF 22.9.E1](https://dlmf.nist.gov/22.9.E1):
  The functions s,c,d sampled at z+N(m−1)K/p, N=2 or4, are `DLMF.JacobiElliptic.jacobiCyclicArg`, `DLMF.JacobiElliptic.jacobiCyclicS`, `DLMF.JacobiElliptic.jacobiCyclicC`, `DLMF.JacobiElliptic.jacobiCyclicD` ([source](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L30)). κ=dn(2K/3,k) is `DLMF.JacobiElliptic.jacobiCyclicKappa`. The rank of a cyclic identity is the largest number of elliptic-function factors in a term; no separate local syntactic rank object is defined.

  [DLMF 22.9.E1](https://dlmf.nist.gov/22.9.E1): The cyclic argument `z + N p⁻¹ (m - 1) K(k)` of DLMF 22.9.1–22.9.6 (`N = 2` or `4`).
  [`DLMF.JacobiElliptic.jacobiCyclicArg`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L30).

  [DLMF 22.9.E1](https://dlmf.nist.gov/22.9.E1): `s_{m,p}^{(N)} = sn(z + N p⁻¹(m - 1)K, k)` (DLMF 22.9.1, 22.9.4).
  [`DLMF.JacobiElliptic.jacobiCyclicS`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L34).

  [DLMF 22.9.E2](https://dlmf.nist.gov/22.9.E2): `c_{m,p}^{(N)} = cn(z + N p⁻¹(m - 1)K, k)` (DLMF 22.9.2, 22.9.5).
  [`DLMF.JacobiElliptic.jacobiCyclicC`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L38).

  [DLMF 22.9.E3](https://dlmf.nist.gov/22.9.E3): `d_{m,p}^{(N)} = dn(z + N p⁻¹(m - 1)K, k)` (DLMF 22.9.3, 22.9.6).
  [`DLMF.JacobiElliptic.jacobiCyclicD`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L42).

  [DLMF 22.9.E7](https://dlmf.nist.gov/22.9.E7): `κ = dn(2K/3, k)` (DLMF 22.9.7).
  [`DLMF.JacobiElliptic.jacobiCyclicKappa`](DLMF/JacobiElliptic/Cyclic/QuarterPeriodAndThreePoint.lean#L46).

### §22.15 Inverse Functions

<!-- retained entry 155 -->
- **Principal arcsn, arccn and arcdn**, [22.15.1–10](https://dlmf.nist.gov/22.15.E1):
  `DLMF.Elliptic.Real.jacobiArcsnm` in
  [SpecialValues](DLMF/Elliptic/SpecialValues.lean#L84),
  `DLMF.JacobiElliptic.Real.jacobiArccnm`, `jacobiArcdnm` in
  [Inverse](DLMF/JacobiElliptic/Inverse.lean#L42). They use parameter m,
  with the DLMF principal intervals and range conditions in theorems.
  The other nine inverse functions are independently defined there as
  `jacobiArccdm`, `jacobiArcsdm`, `jacobiArcndm`, `jacobiArcdcm`,
  `jacobiArcncm`, `jacobiArcscm`, `jacobiArcnsm`, `jacobiArcdsm`,
  `jacobiArccsm`. General real solution sets are theorem characterizations;
  no multivalued complex inverse object is defined.

### §22.16 Related Functions

<!-- retained entry 156 -->
- **Jacobi amplitude**, [22.16.1 and continuation prose](https://dlmf.nist.gov/22.16.E1):
  `DLMF.Elliptic.Real.jacobiAmm` in
  [Jacobi](DLMF/Elliptic/Basic/Amplitude.lean#L140), the inverse order isomorphism of F
  when `m<1`. This is the unwrapped real amplitude, not principal arcsine
  of sn on the whole real line.

<!-- retained entry 157 -->
- **Jacobi zeta Z**, [22.16.32](https://dlmf.nist.gov/22.16.E32):
  `DLMF.JacobiElliptic.Real.jacobiZetaFunctionk`, using the independently
  defined integral `Real.jacobiEpsilonk` in
  [Related](DLMF/JacobiElliptic/Related.lean#L284).
  Epsilon is the exact integral of dn² and supplies the referenced quantity
  in the definition; it is distinct from the scaled argument called `jacobiZetak`.

### §22.17 Moduli Outside the Interval [0,1]

- **Imaginary-modulus transformation**, [DLMF 22.17.E5](https://dlmf.nist.gov/22.17.E5):
  k₁=k/√(1+k²) is `DLMF.JacobiElliptic.jacobiImagModulusk` ([source](DLMF/JacobiElliptic/OutsideModuli.lean#L114)); Lean selects the principal square root, whereas DLMF permits either consistent choice. Reciprocal and negative moduli are substitutions in the same functions, not new function families.

  [DLMF 22.17.E5](https://dlmf.nist.gov/22.17.E5): The modulus `k₁ = k/√(1 + k²)` of DLMF 22.17.5 for complex `k` (principal square root; DLMF 22.17(i): either value of the square root can be chosen).
  [`DLMF.JacobiElliptic.jacobiImagModulusk`](DLMF/JacobiElliptic/OutsideModuli.lean#L114).

### §22.18 Mathematical Applications

- **Elliptic curves, Jacobian normal form and Jacobi–Abel addition**, [DLMF 22.18.iv](https://dlmf.nist.gov/22.18.iv):
  The curves y²=P(x) of nonsingular degree3 or4 and the Jacobian normal form y²=(1−x²)(1−k²x²) are defined geometrically here. The rational addition formulas22.18.8 have no dedicated local Jacobian-curve group construction. Mathlib's Weierstrass curve/group APIs concern another presentation and need a change-of-variables bridge. The ellipse and lemniscate parametrizations in §§22.18(i–iii) use the existing Jacobi functions; no additional local named parametrized curves were found.

### §22.19 Physical Applications

- **Pendulum, quartic oscillator and hyperelliptic inverse functions**, [DLMF 22.19.i](https://dlmf.nist.gov/22.19.i):
  DLMF specifies the pendulum energy E=θ′²/2+1−cos θ and the separatrix α=π, then quartic potentials V(x)=±x²/2±βx⁴/4 with η=βa²/2. They have no dedicated local definitions. Hyperelliptic functions in §22.19(iv) are inverses of z=∫₀ᵘ(f(x))^(−1/2)dx for polynomials of degree>4; no corresponding local inverse construction was found. These application definitions are descriptive, without acquiring the mechanics results.

### §22.20 Methods of Computation

- **Complex AGM and backward amplitudes**, [DLMF 22.20.E1](https://dlmf.nist.gov/22.20.E1):
  The complex aₙ,bₙ,cₙ iteration chooses the geometric square root by the nearby-argument convention, with cₙ=(aₙ₋₁−bₙ₋₁)/2 and limit M. The Mathlib/local real AGM objects listed at §19.8 cover positive real data only; there is no local full complex branch-tracked AGM. For positive ordered real data these cₙ agree with §19.8, since cₙ₊₁=(aₙ−gₙ)/2. The additional issue here is complex square-root branch tracking. The finite backward φₙ recurrence of 22.20.3–4 is a numerical evaluation construction, not a separate exact Jacobi-amplitude definition in Lean. Decimal examples/tables remain excluded: numerical. §§22.5–6,22.8,22.10–14,22.21–22 otherwise give identities, expansions, integrals or software rather than additional function families. The alternative integral/continuous-amplitude representations are distinguished at §22.16.

## Chapter 23 — Weierstrass elliptic and modular functions

Expanded review: all 24 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§23.1–23.24 checked; matching sections are §23.2 and §23.15.

### §23.2 Definitions and Periodic Properties

<!-- retained entry 158 -->
- **Lattice and half-periods**, [§23.2(i), 23.2.1–3](https://dlmf.nist.gov/23.2.i):
  `DLMF.Weierstrass.HalfPeriods`, `HalfPeriods.ω₂`, `tau`, `nome`,
  `periodPair`, and `lattice` in
  [LatticesAndSigma](DLMF/Weierstrass/Basic/Periods.lean#L23).
  Mathlib `PeriodPair` and `PeriodPair.lattice` in
  [Weierstrass](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean#L60)
  store **full periods**, without the orientation requirement; the local
  conversion supplies `2ω₁,2ω₃` and retains DLMF's positive ratio orientation.

<!-- retained entry 159 -->
- **Weierstrass ℘**, [23.2.4](https://dlmf.nist.gov/23.2.E4): Mathlib
  `PeriodPair.weierstrassP` and `derivWeierstrassP` in
  [Weierstrass](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean#L268).
  The local `HalfPeriods.weierstrassP`, `derivWeierstrassP` are abbreviations
  through the full-period conversion. Invariant-based alternatives
  `weierstrassPInvariants`, `weierstrassZetaInvariants`, `weierstrassSigmaInvariants`
  in [EllipticFunctionsAndInvariants](DLMF/Weierstrass/Basic/Invariants.lean#L26)
  choose a lattice with specified invariants, rather than a new lattice sum.

<!-- retained entry 160 -->
- **Weierstrass ζ and σ**, [23.2.5–6](https://dlmf.nist.gov/23.2.E5):
  `DLMF.Weierstrass.weierstrassZeta`, `weierstrassSigma` in
  [LatticesAndSigma](DLMF/Weierstrass/Basic/Functions.lean#L21),
  a lattice sum and product respectively; half-period methods are abbreviations.
  Totalized lattice-point values do not represent poles of ζ or ℘.

<!-- retained entry 161 -->
- **Elliptic function and quasi-period constants ηⱼ**,
  [§23.2(iii) prose and 23.2.12](https://dlmf.nist.gov/23.2.iii):
  η is `DLMF.Weierstrass.HalfPeriods.eta` in
  [EllipticFunctionsAndInvariants](DLMF/Weierstrass/Basic/Functions.lean#L71).
  Meromorphicity and double periodicity are expressed through their standard
  predicates; there is no separate local class called `EllipticFunction`.

### §23.3 Differential Equations

- **Lattice Discriminant**, [DLMF 23.3.E4](https://dlmf.nist.gov/23.3.E4): The discriminant `Δ = g₂³ - 27g₃²` of a lattice (DLMF 23.3.4).
  [`DLMF.Weierstrass.latticeDiscriminant`](DLMF/Weierstrass/Basic/Functions.lean#L77).

- **Weierstrass half-period values eⱼ**, [DLMF 23.3.E9](https://dlmf.nist.gov/23.3.E9): The lattice roots `e_j = ℘(ω_j)` (DLMF 23.3.9), `j = 1, 2, 3`.
  [`DLMF.Weierstrass.HalfPeriods.e`](DLMF/Weierstrass/Basic/Functions.lean#L67).

### §23.5 Special Lattices

- **Special lattice classes**, [DLMF 23.5](https://dlmf.nist.gov/23.5):
  `DLMF.Weierstrass.HalfPeriods.IsRectangular`, `DLMF.Weierstrass.HalfPeriods.IsLemniscatic`, `DLMF.Weierstrass.HalfPeriods.IsRhombic`, `DLMF.Weierstrass.HalfPeriods.IsEquianharmonic` ([source](DLMF/Weierstrass/SpecialLattices.lean#L168)) express the four half-period geometries; `DLMF.Weierstrass.HalfPeriods.rectangular` and `DLMF.Weierstrass.HalfPeriods.rhombic` construct examples from positive real parameters. DLMF also names the pseudo-lemniscatic rhombic case2ω₃=(1+i)ω₁; no separate local predicate was found. Conjugation-invariant lattices are expressed directly as equality with the conjugate lattice, with real invariants as an equivalent property.

### §23.6 Relations to Other Functions

- **Weierstrass/Jacobi moduli and alternate lattices**, [DLMF 23.6.E16](https://dlmf.nist.gov/23.6.E16):
  k²=(e₂−e₃)/(e₁−e₃), k′²=(e₁−e₂)/(e₁−e₃); the actual theta-based abbreviations are `DLMF.Weierstrass.HalfPeriods.modulus`, `DLMF.Weierstrass.HalfPeriods.comodulus`, `DLMF.Weierstrass.HalfPeriods.quarterK` ([source](DLMF/Weierstrass/Relations/JacobiIdentities.lean#L157)). Their bridge theorems fix branches via τ rather than choosing an arbitrary root of the displayed ratio. The three lattices L₁,L₂,L₃ in 23.6.27–29 use explicit `PeriodPair` constructions in the relation statements. The inverse elliptic-integral variable w in 23.6.36 depends on its path and square-root determination; no single path-independent local inverse function is defined.

### §23.9 Laurent and Other Power Series

- **Laurent and sigma coefficients**, [DLMF 23.9.E1](https://dlmf.nist.gov/23.9.E1):
  The lattice-sum cₙ is `DLMF.Weierstrass.laurentCoeff` ([source](DLMF/Weierstrass/Series.lean#L340)); a_{m,n}, including negative-index zero conventions, is `DLMF.Weierstrass.sigmaCoeff` ([source](DLMF/Weierstrass/Series.lean#L736)). The Laurent theorems require the argument norm to be smaller than every nonzero lattice-point norm; no particular minimizing point z₀ is selected. These are exact series coefficients, within scope despite adjacent coefficient tables.

  [DLMF 23.9.E1](https://dlmf.nist.gov/23.9.E1): The Laurent coefficients `c_n = (2n - 1) ∑_{w ∈ 𝕃∖{0}} w^{-2n}` (DLMF 23.9.1), `n ≥ 2` (Mathlib's `G (2n)` sums over `𝕃` with the `w = 0` term `0`).
  [`DLMF.Weierstrass.laurentCoeff`](DLMF/Weierstrass/Series.lean#L340).

  [DLMF 23.9.E8](https://dlmf.nist.gov/23.9.E8): The coefficients `a_{m,n}` of the power series of `σ` (DLMF 23.9.8): `a_{0,0} = 1`, `a_{m,n} = 0` if `m < 0` or `n < 0`, and for `(m, n) ≠ (0, 0)` `a_{m,n} = 3(m+1)a_{m+1,n-1} + (16/3)(n+1)a_{m-2,n+1} - (1/3)(2m+3n-1)(4m+6n-1)a_{m-1,n}`. The recursion is well founded in the weight `2m + 3n`.
  [`DLMF.Weierstrass.sigmaCoeff`](DLMF/Weierstrass/Series.lean#L736).

### §23.10 Addition Theorems and Other Identities

- **Multiplication constants Aₙ and G**, [DLMF 23.10.E14](https://dlmf.nist.gov/23.10.E14):
  The actual constructions are `DLMF.Weierstrass.HalfPeriods.nTupleConst`, `DLMF.Weierstrass.HalfPeriods.nTupleG` ([source](DLMF/Weierstrass/Addition.lean#L844)). The local Aₙ deliberately corrects DLMF's printed product: omit only (j,ℓ)=(0,0), rather than every diagonal pairℓ=j. This is a deliberate statement/source discrepancy, rather than an exact transcription of the printed product. G is the exact infinite product ∏(1−q^(2n)), with its convergence hypotheses supplied by theorems.

  [DLMF 23.10.E14](https://dlmf.nist.gov/23.10.E14): The constant `A_n` of 23.10.13, by the **corrected** DLMF 23.10.14: `A_n = n ∏_{(j,ℓ) ≠ (0,0)} 1/σ((2jω₁ + 2ℓω₃)/n)`, `0 ≤ j, ℓ < n`. Corrected from the printed DLMF formula: the printed index set `ℓ ≠ j` is wrong (relative error 0.71 at `n = 2`); the product runs over `(j, ℓ) ≠ (0, 0)`, excluding only the zero of `σ`.
  [`DLMF.Weierstrass.HalfPeriods.nTupleConst`](DLMF/Weierstrass/Addition.lean#L844).

  [DLMF 23.10.E16](https://dlmf.nist.gov/23.10.E16): `G = ∏_{n≥1} (1 - q^{2n})`, `q = e^{πiω₃/ω₁}` (DLMF 23.10.16).
  [`DLMF.Weierstrass.HalfPeriods.nTupleG`](DLMF/Weierstrass/Addition.lean#L862).

### §23.11 Integral Representations

- **Integral-representation kernels**, [DLMF 23.11.E1](https://dlmf.nist.gov/23.11.E1):
  f₁(s,τ),f₂(s,τ) are `DLMF.Weierstrass.integralKernelOne`, `DLMF.Weierstrass.integralKernelTwo` ([source](DLMF/Weierstrass/Integrals.lean#L35)). The integral formulas for ℘ and ζ are bridge theorems for the existing functions, with strip and normalization restrictions; they are not a second definition selected everywhere.

  [DLMF 23.11.E1](https://dlmf.nist.gov/23.11.E1): `f₁(s, τ) = cosh²(τs/2)/(1 - 2e^{-s}cosh(τs) + e^{-2s})` (DLMF 23.11.1).
  [`DLMF.Weierstrass.integralKernelOne`](DLMF/Weierstrass/Integrals.lean#L35).

  [DLMF 23.11.E1](https://dlmf.nist.gov/23.11.E1): `f₂(s, τ) = cos²(s/2)/(1 - 2e^{iτs}cos s + e^{2iτs})` (DLMF 23.11.1).
  [`DLMF.Weierstrass.integralKernelTwo`](DLMF/Weierstrass/Integrals.lean#L40).

### §23.15 Definitions

<!-- retained entry 162 -->
- **Modular transformation, modular function, modular form and cusp form**,
  [23.15.3–5 and prose](https://dlmf.nist.gov/23.15.i):
  `DLMF.Weierstrass.mobius`, `IsModularFunction`, `IsModularForm`,
  `IsCuspForm` in [ModularFunctions](DLMF/Weierstrass/ModularFunctions.lean#L69).
  They follow DLMF's multiplier and half-integer exponent convention with
  doubled integer weight `ℓ₂`; this is not simply an alias for Mathlib's
  integral-weight `ModularForm` and `CuspForm` structures.

<!-- retained entry 163 -->
- **Modular λ and Klein J**, [23.15.6–7](https://dlmf.nist.gov/23.15.E6):
  `DLMF.Weierstrass.modularLambda`, `kleinJ` in
  [ModularFunctions](DLMF/Weierstrass/ModularFunctions.lean#L111).
  J uses DLMF's normalization, so the classical j-invariant has an extra
  factor 1728. `DLMFMathlib`'s `p3wJ` in
  [P3wJSurjective](DLMFMathlib/NumberTheory/ModularForms/P3wJSurjective.lean#L32)
  is an independent Eisenstein-series quotient with that same J normalization.

<!-- retained entry 164 -->
- **Dedekind eta and θ₁ derivative**, [23.15.8–9](https://dlmf.nist.gov/23.15.E8):
  the derivative is `DLMF.Theta.jacobiThetaOneDerivNullTau`; Mathlib's
  `ModularForm.eta` construction in
  [DedekindEta](.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/DedekindEta.lean#L57)
  is used directly. The local identities identify the correct cube-root
  branch, rather than defining eta by a principal cube root without qualification.

### §23.18 Modular Transformations

- **Eta multiplier and Dedekind sum**, [DLMF 23.18.E6](https://dlmf.nist.gov/23.18.E6):
  ε(A) and s(d,c), c>0, are `DLMF.Weierstrass.etaMultiplier`, `DLMF.Weierstrass.dedekindSum` ([source](DLMF/Weierstrass/ModularFunctions.lean#L751)). The sum uses every r=1,…,c−1, not just residues coprime to c. The six anharmonic λ transforms of 23.18.1–2 also have existing exact helpers `DLMF.Weierstrass.p3w_anharm`, `DLMF.Weierstrass.p3w_anharmSL` ([source](DLMF/Weierstrass/ModularFunctions.lean#L498)); the arguments encode the matrix parity class.

  [DLMF 23.18.E6](https://dlmf.nist.gov/23.18.E6): The eta multiplier `ε(𝒜) = exp(πi((a + d)/(12c) + s(-d, c)))` (DLMF 23.18.6), `c > 0`.
  [`DLMF.Weierstrass.etaMultiplier`](DLMF/Weierstrass/ModularFunctions.lean#L757).

  [DLMF 23.18.E7](https://dlmf.nist.gov/23.18.E7): The Dedekind sum `s(d, c) = ∑_{r=1}^{c-1} (r/c)(dr/c - ⌊dr/c⌋ - 1/2)` (DLMF 23.18.7, as corrected in DLMF V1.0.11: no coprimality condition on `r`), for `c > 0`.
  [`DLMF.Weierstrass.dedekindSum`](DLMF/Weierstrass/ModularFunctions.lean#L751).

### §23.20 Mathematical Applications

- **Elliptic curve coordinates, group law, torsion and rank**, [DLMF 23.20.E1](https://dlmf.nist.gov/23.20.E1):
  y²=x³+ax+b and its homogeneous form y²z=x³+axz²+bz³ are represented by Mathlib's `WeierstrassCurve` with a₁=a₂=a₃=0,a₄=a,a₆=b. Its nonsingular point type carries the chord/tangent group law, identity at infinity, negation and slope. A separate project-local curve wrapper was not found. Torsion is the finite-order subgroup, I denotes integral-coordinate points, K rational-coordinate points, and r is the rank of K in the prose decomposition. Those arithmetic point-set constructions and their analytic ℘ uniformization are not implemented locally. The Δ=4a³+27b² convention in this paragraph differs by a factor−16 from the standard Weierstrass discriminant.

- **Modular equations and ellipsoidal coordinates**, [DLMF 23.20.iv](https://dlmf.nist.gov/23.20.iv):
  A degree-p modular equation is an algebraic relation between α=λ(pτ),β=λ(τ); u,v are their fourth roots in 23.20.5–8. No independently named local modular-equation polynomial family was found. The ellipsoidal coordinates ξ,η,ζ of [23.21.1](https://dlmf.nist.gov/23.21.E1) are the three rootsρ of x²/(ρ−e₁)+y²/(ρ−e₂)+z²/(ρ−e₃)=1, with f(ρ)=2√((ρ−e₁)(ρ−e₂)(ρ−e₃)); no local coordinate chart/selected roots were found. The substitutionsξ=℘(u),η=℘(v),ζ=℘(w) do not create new ℘ functions. These application definitions are recorded descriptively.

### §23.22 Methods of Computation

- **Reduced lattice generators and classical inversion**, [DLMF 23.22.ii](https://dlmf.nist.gov/23.22.ii):
  DLMF selects a shortest nonzero generator and then a shortest independent upper-half-plane ratio, allowing its stated ties. Mathlib's period pairs and modular fundamental-domain APIs encode relevant data, but no local canonical-generator choice following this procedure was found. The classical inversion problem reconstructs generators from g₂,g₃; the existing `DLMF.Weierstrass.periodPairOfInvariants` choice behind the retained invariant-parametrized functions is an existence-based mathematical construction, not this numerical algorithm. The exact Γ expressions for degenerate-invariant cases are within scope; the worked decimal example is excluded: numerical. §§23.4,23.7–8,23.12–14,23.16–17,23.19,23.23–24 otherwise add graphs/identities/asymptotics/software rather than new function families.

## Chapter 24 — Bernoulli and Euler polynomials

Expanded review: all 21 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§24.1–24.21 checked; the matching section is §24.2, including
its tables. Exact entries instantiate the definitions; decimal approximations
are numerical and introduce no further functions.

### §24.1 Special Notation

- **Historical Bernoulli-number convention**, [§24.1](https://dlmf.nist.gov/24.1): the older positive sequence 1/6,1/30,1/42,… uses the absolute even-index values |B₂ₙ|, with its own indexing, rather than DLMF/Mathlib's signed `bernoulli n`. This is a notational warning, not a new local sequence definition.

### §24.2 Definitions and Generating Functions

<!-- retained entry 165 -->
- **Bernoulli numbers and polynomials**, [24.2.1–5](https://dlmf.nist.gov/24.2.E1):
  Mathlib `bernoulli` in
  [Bernoulli](.lake/packages/mathlib/Mathlib/NumberTheory/Bernoulli.lean#L195),
  `Polynomial.bernoulli` in
  [BernoulliPolynomials](.lake/packages/mathlib/Mathlib/NumberTheory/BernoulliPolynomials.lean),
  the real evaluation `bernoulliFun` in
  [ZetaValues](.lake/packages/mathlib/Mathlib/NumberTheory/ZetaValues.lean#L48),
  and complex-evaluation wrapper `DLMF.BernoulliEuler.bernoulliPolyB` in
  [Basic](DLMF/BernoulliEuler/Basic.lean#L49). DLMF uses `B₁=-1/2`;
  Mathlib `bernoulli'` has the other sign convention and is not its direct equivalent.
  The native formal generating function `bernoulliPowerSeries` is defined in
  [Bernoulli](.lake/packages/mathlib/Mathlib/NumberTheory/Bernoulli.lean#L266).

<!-- retained entry 166 -->
- **Euler numbers and polynomials**, [24.2.6–10](https://dlmf.nist.gov/24.2.E6):
  `Polynomial.euler`, `eulerNumber`, `eulerFun` in
  [EulerPolynomials](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L59),
  and complex wrapper `DLMF.BernoulliEuler.eulerPolyE` in
  [Basic](DLMF/BernoulliEuler/Basic.lean#L54). The number normalization is
  `2ⁿ Eₙ(1/2)`, retaining DLMF's alternating even Euler numbers.

<!-- retained entry 167 -->
- **Periodic Bernoulli and antiperiodic Euler functions**,
  [24.2.11–12](https://dlmf.nist.gov/24.2.E11):
  `DLMF.BernoulliEuler.periodicBernoulliB`, `periodicEulerE` in
  [Basic](DLMF/BernoulliEuler/Basic.lean#L236), using fractional part and
  the integer-part sign for Euler. Their values at integers follow the
  half-open interval convention, especially relevant in degree one.
  The real definitions `periodicBernoulli` in
  [EulerMaclaurin](DLMFMathlib/Analysis/EulerMaclaurin.lean#L47) and
  `antiperiodicEuler` in [BooleSummation](DLMFMathlib/Analysis/BooleSummation.lean#L39)
  repeat these same expressions. Mathlib's `periodizedBernoulli` in
  [ZetaValues](.lake/packages/mathlib/Mathlib/NumberTheory/ZetaValues.lean#L274)
  is the corresponding function on `UnitAddCircle`; the local equality
  theorem makes the change of domain explicit.

<!-- retained entry 168 -->
- **Coefficient arrays bₙₖ and eₙₖ**, [Tables 24.2.5–6](https://dlmf.nist.gov/24.2.T5):
  coefficients of `Polynomial.bernoulli n` and `Polynomial.euler n`, via
  `Polynomial.coeff`; no separate local coefficient-array definitions.

- **Polynomial coefficient arrays and exact tables**, [Tables 24.2.5–6](https://dlmf.nist.gov/24.2.T5): bₙ,ₖ=[xᵏ]Bₙ(x) and eₙ,ₖ=[xᵏ]Eₙ(x) are Mathlib `Polynomial.coeff` applied to `Polynomial.bernoulli n` and the project's `Polynomial.euler n`. No separate array wrappers are needed. The integer/rational tables give exact examples; decimal columns in Table 24.2.3 are excluded as numerical, without excluding the exact numerators/denominators.

### §24.4 Basic Properties

- **Bernoulli and Euler umbral substitutions**, [DLMF 24.4.viii](https://dlmf.nist.gov/24.4.viii):
  The umbral substitution of DLMF §24.4(viii) for Bernoulli polynomials: expand the complex
  polynomial `P` in powers of its variable and replace each power `yⁿ` by `Bₙ(x)`; this is the
  meaning of `P(B(x))` with `(B(x))ⁿ = Bₙ(x)`.
  `DLMF.BernoulliEuler.umbralBernoulli` ([definition](DLMF/BernoulliEuler/Properties.lean#L1270)).

  [DLMF 24.4.viii](https://dlmf.nist.gov/24.4.viii):
  The umbral substitution `(E(x))ⁿ = Eₙ(x)` of DLMF §24.4(viii).
  `DLMF.BernoulliEuler.umbralEuler` ([definition](DLMF/BernoulliEuler/Properties.lean#L1276)).

### §24.9 Inequalities

- **Exact Bernoulli inequality parameter β**, [DLMF 24.9.E9](https://dlmf.nist.gov/24.9.E9):
  The constant `β = 2 + ln(1 - 6/π²)/ln 2` of DLMF 24.9.9 (exact definition; the decimal value
  `0.6491…` is numerical and not acquired).
  `DLMF.BernoulliEuler.bernoulliIneqBeta` ([definition](DLMF/BernoulliEuler/Inequalities.lean#L584)).

### §24.10 Arithmetic Properties

- **Congruence of rationals with invertible denominators**, [DLMF 24.10.i](https://dlmf.nist.gov/24.10.i):
  Congruence of rational numbers in DLMF §24.10: `a ≡ b (mod M)` when `M` divides the
  numerator of `a - b`.
  `DLMF.BernoulliEuler.RatModEq` ([definition](DLMF/BernoulliEuler/Arithmetic.lean#L41)).

- **Reduced numerators and positive denominators of Bernoulli numbers**, [24.10.7 and prose](https://dlmf.nist.gov/24.10.E7), [24.19.1–2](https://dlmf.nist.gov/24.19.E1): N₂ₙ and D₂ₙ are `(bernoulli (2*n)).num` and `.den`, Mathlib's canonical rational numerator/denominator. Their prime-product formulas do not define a different sequence. Rational congruence is the existing `DLMF.BernoulliEuler.RatModEq`, not merely a coercion to a residue field when a denominator is noninvertible.

### §24.12 Zeros

- **Bernoulli real-zero counting function**, [DLMF 24.12.i](https://dlmf.nist.gov/24.12.i):
  DLMF §24.12(i): `R(n)`, the total number of real zeros of `Bₙ(x)` (with multiplicity).
  `DLMF.BernoulliEuler.bernoulliRealZeroCount` ([definition](DLMF/BernoulliEuler/Zeros/RealZeros.lean#L45)).

- **Bernoulli real-zero sets above and below the endpoint**, [DLMF 24.12.E1](https://dlmf.nist.gov/24.12.E1):
  DLMF 24.12.1: the real zeros `x_1^{(n)} ≤ x_2^{(n)} ≤ ⋯` of `Bₙ(x)` in `[1/2, ∞)`,
  increasing and counted with multiplicity.
  `DLMF.BernoulliEuler.bernoulliRealZerosGE` ([definition](DLMF/BernoulliEuler/Zeros/RealZeros.lean#L34)).

  [DLMF 24.12.E1](https://dlmf.nist.gov/24.12.E1):
  DLMF §24.12(i): `x_j^{(n)}`, the `j`-th real zero of `Bₙ` in `[1/2, ∞)` (`j ≥ 1`); the
  totalized value `0` is returned when there is no such zero.
  `DLMF.BernoulliEuler.bernoulliRealZero` ([definition](DLMF/BernoulliEuler/Zeros/RealZeros.lean#L40)).

- **Euler real-zero sets above and below the endpoint**, [DLMF 24.12.E7](https://dlmf.nist.gov/24.12.E7):
  DLMF 24.12.7: the real zeros `y_1^{(n)} ≤ y_2^{(n)} ≤ ⋯` of `Eₙ(x)` in `[1/2, ∞)`,
  increasing and counted with multiplicity.
  `DLMF.BernoulliEuler.eulerRealZerosGE` ([definition](DLMF/BernoulliEuler/Zeros/RealZeros.lean#L50)).

  [DLMF 24.12.E7](https://dlmf.nist.gov/24.12.E7):
  DLMF §24.12(ii): `y_j^{(n)}`, the `j`-th real zero of `Eₙ` in `[1/2, ∞)` (`j ≥ 1`); the
  totalized value `0` is returned when there is no such zero.
  `DLMF.BernoulliEuler.eulerRealZero` ([definition](DLMF/BernoulliEuler/Zeros/RealZeros.lean#L56)).

### §24.14 Sums

- **Hankel/persymmetric determinants of Bernoulli and Euler numbers**, [24.14.11–12](https://dlmf.nist.gov/24.14.E11): det[aᵣ₊ₛ] denotes an (n+1)×(n+1) matrix with indices 0,…,n. It is expressible by `Matrix.det (fun i j : Fin (n+1) => a (i+j))`. This repeats the general Hankel construction, with an order shift relative to `DLMF.OrthogonalPolynomials.hankelDeterminant` (whose argument is the matrix size). No separate determinant function is introduced for these two sequences.

### §24.15 Related Sequences of Numbers

- **Genocchi Number**, [DLMF 24.15.E2](https://dlmf.nist.gov/24.15.E2):
  DLMF 24.15.2: the Genocchi numbers `Gₙ = 2(1 - 2ⁿ) Bₙ`. (DLMF defines `Gₙ` by the
  generating function 24.15.1, proved as `hasSum_genocchiNumber`.)
  `DLMF.BernoulliEuler.genocchiNumber` ([definition](DLMF/BernoulliEuler/RelatedNumbers.lean#L52)).

- **Tangent Number**, [DLMF 24.15.E4](https://dlmf.nist.gov/24.15.E4):
  DLMF 24.15.4, 24.15.5: the tangent numbers, `T₂ₙ₋₁ = (-1)ⁿ⁻¹ 2²ⁿ(2²ⁿ - 1)/(2n) · B₂ₙ`
  (`n ≥ 1`) and `T₂ₙ = 0`. (DLMF defines `Tₙ` by the generating function 24.15.3, proved as
  `hasSum_tangentNumber`.)
  `DLMF.BernoulliEuler.tangentNumber` ([definition](DLMF/BernoulliEuler/RelatedNumbers.lean#L102)).

- **Stirling and Fibonacci cross-references**, [§24.15(iii)–(iv)](https://dlmf.nist.gov/24.15.iii): s(n,m) is the signed Stirling number of the first kind and S(n,m) is of the second kind, with the conventions catalogued in §26.8. Fibonacci u₀=0,u₁=1 is Mathlib `Nat.fib`; Lucas v₀=2,v₁=1 is the existing `DLMF.BernoulliEuler.lucasNumber`. This recurrence definition is distinct from the tangent-number Tₙ convention, which is indexed by every Taylor degree and vanishes for even n.

  [DLMF 24.15.iv](https://dlmf.nist.gov/24.15.iv):
  DLMF §24.15(iv): the Lucas numbers `v₀ = 2`, `v₁ = 1`, `vₙ₊₁ = vₙ + vₙ₋₁`. (The Fibonacci
  numbers `uₙ` are Mathlib's `Nat.fib`.)
  `DLMF.BernoulliEuler.lucasNumber` ([definition](DLMF/BernoulliEuler/RelatedNumbers.lean#L455)).

### §24.16 Generalizations

- **Integer order versus complex-order/index extensions**, [§24.16(i), prose](https://dlmf.nist.gov/24.16.i): the displayed higher-order Bernoulli/Euler polynomials use nonnegative integer order ℓ; the Nörlund polynomial Bₙ⁽ˣ⁾ is polynomial in the order x with natural index n. The prose also references extensions to arbitrary complex x,n,ℓ; those analytic continuations are not supplied by the existing natural-index/int-order wrappers merely because their values can be coerced to ℂ. No corresponding general complex-index family was identified.

- **Higher-order Bernoulli polynomials**, [DLMF 24.16.E1](https://dlmf.nist.gov/24.16.E1):
  DLMF 24.16.1: the Bernoulli polynomials of order `ℓ`,
  `B_n^{(ℓ)}(x) = ∑ₖ (n choose k) B_k^{(ℓ)} x^{n-k}`.
  `DLMF.BernoulliEuler.bernoulliOrder` ([definition](DLMF/BernoulliEuler/Generalizations/HigherOrder.lean#L47)).

- **Higher-order Euler polynomials**, [DLMF 24.16.E2](https://dlmf.nist.gov/24.16.E2):
  DLMF 24.16.2: the Euler polynomials of order `ℓ`,
  `E_n^{(ℓ)}(x) = ∑ₖ (n choose k) E_k^{(ℓ)} x^{n-k}`.
  `DLMF.BernoulliEuler.eulerOrder` ([definition](DLMF/BernoulliEuler/Generalizations/HigherOrder.lean#L75)).

- **Higher-order Bernoulli and Euler numbers**, [DLMF 24.16.E3](https://dlmf.nist.gov/24.16.E3):
  DLMF 24.16.3: the Bernoulli numbers of order `ℓ`, `B_n^{(ℓ)} = B_n^{(ℓ)}(0)`.
  `DLMF.BernoulliEuler.bernoulliNumberOrder` ([definition](DLMF/BernoulliEuler/Generalizations/HigherOrder.lean#L43)).

  [DLMF 24.16.E3](https://dlmf.nist.gov/24.16.E3):
  DLMF 24.16.3: the Euler numbers of order `ℓ`, `E_n^{(ℓ)} = E_n^{(ℓ)}(0)`, the coefficients of
  `(2/(eᵗ+1))^ℓ`.
  `DLMF.BernoulliEuler.eulerNumberOrder` ([definition](DLMF/BernoulliEuler/Generalizations/HigherOrder.lean#L69)).

- **DLMF 24.16.5: the Bernoulli numbers of the second kind**, [DLMF 24.16.E5](https://dlmf.nist.gov/24.16.E5):
  DLMF 24.16.5: the Bernoulli numbers of the second kind,
  `bₙ = ∫₀¹ (x choose n) dx = (1/n!) ∑ₖ [xᵏ](x(x-1)⋯(x-n+1))/(k+1)`.
  `DLMF.BernoulliEuler.bernoulliSecondKind` ([definition](DLMF/BernoulliEuler/Generalizations/HigherOrder.lean#L550)).

- **Degenerate Bernoulli polynomials**, [DLMF 24.16.E7](https://dlmf.nist.gov/24.16.E7):
  DLMF 24.16.7: the degenerate Bernoulli numbers `βₙ(λ)` as polynomials in `λ`:
  `βₙ(λ)/n!` is the `n`-th coefficient of the inverse of `((1 + λt)^{1/λ} - 1)/t`.
  `DLMF.BernoulliEuler.degenerateBernoulli` ([definition](DLMF/BernoulliEuler/Generalizations/HigherOrder.lean#L688)).

- **Nørlund polynomials**, [DLMF 24.16.E9](https://dlmf.nist.gov/24.16.E9):
  DLMF 24.16.9: the Nörlund polynomial `B_n^{(x)}`, as a polynomial in the order `x`, defined
  by `(t/(eᵗ-1))^x = ∑ₙ B_n^{(x)} tⁿ/n!` in the sense of formal power series.
  `DLMF.BernoulliEuler.norlundPolynomial` ([definition](DLMF/BernoulliEuler/Generalizations/HigherOrder.lean#L37)).

- **Character conductor, trivial character and the character modulo four**, [§24.16(ii)](https://dlmf.nist.gov/24.16.ii): generalized Bernoulli objects use a primitive Dirichlet character χ with conductor f. Mathlib `DirichletCharacter` supplies the character and conductor APIs; the trivial character is the multiplicative identity character. The unique nontrivial primitive χ₄ is 1 on 1 mod 4, −1 on 3 mod 4 and zero on even classes. Mathlib `ZMod.χ₄` gives the integral character; the local complex-valued adapter `DLMF.BernoulliEuler.b24b_chi4` in [DegenerateAndCharacter](DLMF/BernoulliEuler/Generalizations/DegenerateAndCharacter.lean#L909) realizes that special character used in 24.16.13. Its periodic residue-class convention is essential to the factor 2^(1−n)/(n+1).

- **Character-generalized Bernoulli numbers**, [DLMF 24.16.E10](https://dlmf.nist.gov/24.16.E10):
  DLMF 24.16.10: the generalized Bernoulli numbers belonging to a Dirichlet character `χ`
  modulo `f`, by the closed form `B_{n,χ} = f^{n-1} ∑_{a=1}^{f} χ(a) Bₙ(a/f)` (DLMF: `χ`
  primitive with conductor `f`; the generating function is `hasSum_bernoulliChar`).
  `DLMF.BernoulliEuler.bernoulliChar` ([definition](DLMF/BernoulliEuler/Generalizations/DegenerateAndCharacter.lean#L867)).

- **Character-generalized Bernoulli polynomials**, [DLMF 24.16.E11](https://dlmf.nist.gov/24.16.E11):
  DLMF 24.16.11: `B_{n,χ}(x) = ∑ₖ (n choose k) B_{k,χ} x^{n-k}`.
  `DLMF.BernoulliEuler.bernoulliCharPoly` ([definition](DLMF/BernoulliEuler/Generalizations/DegenerateAndCharacter.lean#L875)).

- **Other named Bernoulli/Euler generalizations**, [§24.16(iii)](https://dlmf.nist.gov/24.16.iii): the prose lists arbitrary complex-index Bernoulli/Euler functions, q-analogs, conjugate Bernoulli/Euler polynomials, Bernoulli–Hurwitz numbers, poly-Bernoulli numbers, universal Bernoulli numbers, p-adic integer-order Bernoulli numbers, p-adic q-Bernoulli numbers, periodic Bernoulli numbers, cotangent numbers, Bernoulli–Carlitz numbers, Bernoulli–Padé numbers, Bernoulli numbers attached to periodic functions, cyclotomic Bernoulli numbers, Zagier's modified Bernoulli numbers, and multiple-parameter higher-order Bernoulli/Euler polynomials. The page provides references rather than formulas fixing all conventions. No dedicated local equivalents for these additional families were identified; they should not be silently identified with `norlundPolynomial` or the already defined periodic Bernoulli functions.

### §24.17 Mathematical Applications

- **Boole remainder**, [24.17.2](https://dlmf.nist.gov/24.17.E2): Rₘ(n) is the integral of f⁽ᵐ⁾(x) times the shifted antiperiodic Euler function, divided by 2(m−1)!. The existing Boole-summation development under `DLMFMathlib` supplies related formulas; no separate public remainder function was identified. The named periodic factor is `DLMF.BernoulliEuler.periodicEulerE`. This exact summation remainder remains mathematical, although it appears in the applications section.

- **Cardinal splines, Euler splines and Bernoulli monosplines**, [§24.17(ii), 24.17.3–8](https://dlmf.nist.gov/24.17.ii): S-classₙ consists of functions with n−1 continuous derivatives and polynomial pieces of degree at most n between consecutive integers; cardinal monosplines of degree n are xⁿ−S(x), with S in S-classₙ₋₁. Euler splines are the normalized shifted periodic Euler function in 24.17.3; Mₙ is periodic Bₙ−Bₙ(0) for even n and the half-shifted periodic Bₙ for odd n. The minimal-norm F is periodic Bₙ−2⁻ⁿBₙ(0). The periodic factors exist as `DLMF.BernoulliEuler.periodicEulerE` and `periodicBernoulliB`, but no dedicated spline-class/Euler-spline/monospline wrappers were found. These application-note definitions are recorded without adding theorem-acquisition targets.

### §24.19 Methods of Computation

- **Truncated prime product and irregular pairs**, [§24.19(i)–(ii)](https://dlmf.nist.gov/24.19.i): N-tilde₂ₙ is the prime-product expression in 24.19.1 with its second product cut off at p≤floor(2n/(πe))+1. This exact finite expression has no dedicated local wrapper; the rounding identity is separate from numerical approximation claims. An irregular pair (2n,p) in the page's range 2n≤p−3 means B₂ₙ≡0 mod p, expressible using primality, the index inequalities and `DLMF.BernoulliEuler.RatModEq p (bernoulli (2*n)) 0`; no dedicated local pair predicate was found.

## Chapter 25 — Zeta and related functions

Expanded review: all 21 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§25.1–25.21 checked; matching headings are §25.2
(including (i)), §25.11(i), §25.14(i), and §25.15(i).

### §25.1 Special Notation

- **Zeta-related historical notation and derivative conventions**, [§25.1](https://dlmf.nist.gov/25.1): Jonquière's φ(z,s) means Liₛ(z), while Lerch's Φ has three arguments. ψ means digamma except in §25.16, where it is Chebyshev's prime-counting function; primes on Hurwitz ζ in §§25.11(vi),(viii),(xii) differentiate s, not a. These are notation conventions rather than new definitions.

### §25.2 Definition and Expansions

<!-- retained entry 169 -->
- **Riemann zeta**, [25.2.1 and continuation prose](https://dlmf.nist.gov/25.2.E1):
  Mathlib `riemannZeta` in
  [RiemannZeta](.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L121),
  obtained from the continued Hurwitz theory. Its Dirichlet series is a
  theorem representation for `Re s > 1`; `LSeries (fun _ => 1)` is an independent
  generic series construction, not the continued zeta function at other s.

- **Native series versus completed/continued zeta**, [25.2.1 and continuation prose](https://dlmf.nist.gov/25.2.E1), [25.4.4](https://dlmf.nist.gov/25.4.E4): in addition to Mathlib `riemannZeta` and the generic `LSeries` already listed, Mathlib `completedRiemannZeta` and the entire corrected `completedRiemannZeta₀` in [RiemannZeta](.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L64) are distinct completion objects used to define the entire ξ-function, including its removable endpoint values. The literal product s(s−1)Γ(s/2)ζ(s) cannot be used at s=0 or1 by naive totalized evaluation.

<!-- retained entry 170 -->
- **Stieltjes constants**, [25.2.4–5](https://dlmf.nist.gov/25.2.E5):
  `DLMF.Zeta.stieltjesSeq`, `stieltjesConstant` in
  [Riemann](DLMF/Zeta/Riemann.lean#L89), the exact limit with DLMF's
  `(-1)ⁿ/n!` Laurent-coefficient convention.

### §25.4 Reflection Formulas

- **Completed Riemann xi function**, [DLMF 25.4.E4](https://dlmf.nist.gov/25.4.E4):
  DLMF 25.4.4: Riemann's `ξ`-function `ξ(s) = ½ s(s-1) Γ(s/2) π^{-s/2} ζ(s)`, defined as the
  entire function `½ s(s-1) Λ₀(s) + ½`, where `Λ₀ = completedRiemannZeta₀` is Mathlib's entire
  completion `Λ(s) + 1/s + 1/(1-s)` of `Λ(s) = π^{-s/2} Γ(s/2) ζ(s)`. The printed formula is
  `riemannXi_eq`.
  `DLMF.Zeta.riemannXi` ([definition](DLMF/Zeta/Reflection.lean#L54)).

- **Riemann-zeta reflection multiplier**, [DLMF 25.4.E6](https://dlmf.nist.gov/25.4.E6):
  DLMF 25.4.6: the constant `c = -ln(2π) - πi/2` of the derivative reflection formulas.
  `DLMF.Zeta.reflectionConst` ([definition](DLMF/Zeta/Reflection.lean#L97)).

### §25.5 Integral Representations

- **Riemann-zeta auxiliary function ω**, [DLMF 25.5.E14](https://dlmf.nist.gov/25.5.E14):
  DLMF 25.5.14: `ω(x) = ∑_{n≥1} e^{-n²πx}` (for `x > 0`; the `tsum` is `0` where the series
  diverges, i.e. for `x ≤ 0`).
  `DLMF.Zeta.zetaOmega` ([definition](DLMF/Zeta/IntegralReps/PolygammaAndContours.lean#L30)).

- **Keyhole-contour zeta integral**, [DLMF 25.5.iii](https://dlmf.nist.gov/25.5.iii):
  The keyhole loop integral `∫_{-∞}^{(0+)} z^a g(z) dz` around the negative real axis: from
  `-∞` along the lower edge of the cut (`arg z = -π`) to `-δ`, once around the circle `|z| = δ`
  in the positive direction, and back along the upper edge (`arg z = π`) to `-∞`. The power `z^a`
  takes the boundary values `x^a e^{∓iπa}` on the two edges and its principal value
  `δ^a e^{iaθ}`, `-π < θ < π`, on the circle. Parametrized,
  `(e^{-iπa} - e^{iπa}) ∫_δ^∞ x^a g(-x) dx + ∫_{-π}^{π} δ^a e^{iaθ} g(δe^{iθ}) iδe^{iθ} dθ`
  (DLMF §25.5(iii), the contour of 25.5.20–25.5.21).
  `DLMF.Zeta.keyholeLoopIntegral` ([definition](DLMF/Zeta/IntegralReps/PolygammaAndContours.lean#L591)).

### §25.9 Asymptotic Approximations

- **Riemann chi multiplier**, [DLMF 25.9.E2](https://dlmf.nist.gov/25.9.E2):
  DLMF 25.9.2: `χ(s) = π^{s-½} Γ(½ - s/2) / Γ(s/2)`.
  `DLMF.Zeta.riemannChi` ([definition](DLMF/Zeta/Asymptotics.lean#L30)).

### §25.10 Zeros

- **Riemann-zeta zeros in the critical strip**, [DLMF 25.10.i](https://dlmf.nist.gov/25.10.i):
  DLMF §25.10(i): the set of zeros of `ζ` in the critical strip `0 < Re s < 1`.
  `DLMF.Zeta.criticalStripZeros` ([definition](DLMF/Zeta/Zeros.lean#L139)).

- **Trivial zeros, critical strip/line and Riemann hypothesis**, [§25.10(i), prose](https://dlmf.nist.gov/25.10.i): trivial zeros are −2n for positive n, the critical strip is 0<Re s<1 and the critical line is Re s=1/2. The project has the already listed zero sets/counting objects; Mathlib `RiemannHypothesis` in [RiemannZeta](.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L185) is the proposition that nontrivial zeros lie on the line. It is a defined proposition, not a proved assertion. The principal-phase convention for the local Riemann–Siegel theta must be retained; it is not automatically the continuously unwrapped phase used by some authors.

- **Riemann–Siegel Z function**, [DLMF 25.10.E1](https://dlmf.nist.gov/25.10.E1):
  DLMF 25.10.1: `Z(t) = e^{iθ(t)} ζ(½ + it)`.
  `DLMF.Zeta.riemannSiegelZ` ([definition](DLMF/Zeta/Zeros.lean#L150)).

- **Riemann–Siegel theta phase**, [DLMF 25.10.E2](https://dlmf.nist.gov/25.10.E2):
  DLMF 25.10.2: the Riemann–Siegel theta function `θ(t) = ph Γ(¼ + ½it) - ½ t ln π`, with the
  principal value of the phase (`Complex.arg`), as DLMF prescribes.
  `DLMF.Zeta.riemannSiegelTheta` ([definition](DLMF/Zeta/Zeros.lean#L144)).

- **Riemann-zeta zero-counting functions**, [DLMF 25.10.ii](https://dlmf.nist.gov/25.10.ii):
  DLMF §25.10(ii): `N(T)`, the number of zeros of `ζ` in the critical strip with `0 < t < T`,
  counted with multiplicity.
  `DLMF.Zeta.riemannZeroCount` ([definition](DLMF/Zeta/Zeros.lean#L269)).

  [DLMF 25.10.ii](https://dlmf.nist.gov/25.10.ii):
  The number of zeros of `ζ` on the critical line with `0 < t < T`, counted with
  multiplicity.
  `DLMF.Zeta.criticalLineZeroCount` ([definition](DLMF/Zeta/Zeros.lean#L275)).

- **Riemann–Siegel remainder**, [DLMF 25.10.E3](https://dlmf.nist.gov/25.10.E3):
  DLMF 25.10.3: the remainder `R(t) = Z(t) - 2 ∑_{n=1}^{m} cos(θ(t) - t ln n)/√n`,
  `m = ⌊√(t/(2π))⌋`, of the Riemann–Siegel formula (`Z` is real, so its real part is taken).
  `DLMF.Zeta.riemannSiegelRemainder` ([definition](DLMF/Zeta/Zeros.lean#L281)).

### §25.11 Hurwitz Zeta Function

<!-- retained entry 171 -->
- **Hurwitz ζ(s,a)**, [25.11.1](https://dlmf.nist.gov/25.11.E1):
  `DLMF.Confluent.hurwitzZetaComplex` in
  [S25bHurwitzCore](DLMF/Zeta/S25bHurwitzCore.lean#L431), a complex-a
  Euler–Maclaurin limit using principal powers. Mathlib `hurwitzZeta` in
  [HurwitzZeta](.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZeta.lean#L53)
  has a `UnitAddCircle` parameter; comparison with DLMF's positive real a
  requires its fundamental representative and shift terms, not mere coercion.
  The series is a bridge for `Re s > 1`; `s=1` and excluded nonpositive
  integral a require their own mathematical interpretation.

- **Harmonic numbers**, [25.11.33](https://dlmf.nist.gov/25.11.E33): Hₙ=Σₖ₌₁ⁿ1/k is Mathlib `harmonic : ℕ → ℚ` in [Defs](.lake/packages/mathlib/Mathlib/NumberTheory/Harmonic/Defs.lean#L23). Coercion gives the real/complex value required by Hurwitz integral formulas. It is different from the Euler-sum function H(s) introduced in §25.16.

- **Catalan Constant**, [DLMF 25.11.E40](https://dlmf.nist.gov/25.11.E40):
  **Catalan's constant** `G = ∑ (-1)^k/(2k+1)² = β(2)` (Duverney Remark 2.9).
  `DLMF.Constants.catalanConstant` ([definition](DLMF/Constants/Catalan.lean#L30)).

### §25.12 Polylogarithms

- **Dilogarithm names and Clausen's integral**, [25.12.1–2](https://dlmf.nist.gov/25.12.E1), [25.12.9](https://dlmf.nist.gov/25.12.E9): Li₂ is the order-two case of the continued complex polylogarithm; S₂, Spence Sp and L₂ are the alternative names listed by DLMF. Its real integral construction is separately `DLMF.Polylog.Real.dilog`. Clausen's integral Cl₂(θ)=−∫₀ᶿlog(2sin(x/2))dx=Σsin(nθ)/n² is an unnamed interval integral, also the imaginary part of Li₂(eⁱᶿ) on the stated range; no dedicated local or upstream Clausen-integral function was found. `DLMF.Hypergeometric.clausenCoeff` concerns a different Clausen identity.

  [DLMF 25.12.E2](https://dlmf.nist.gov/25.12.E2):
  The real dilogarithm `Li₂(x) = ∫₀ˣ -log(1-t)/t dt`, meaningful for `x ≤ 1` (Duverney (8.13)).
  `DLMF.Polylog.Real.dilog` ([definition](DLMF/Polylog/Dilog.lean#L54)).

- **Gamma normalization of Fermi–Dirac/Bose–Einstein integrals**, [§25.12(iii)](https://dlmf.nist.gov/25.12.iii): the existing `DLMF.Zeta.fermiDiracF` and `boseEinsteinG` include 1/Γ(s+1), exactly as in DLMF. The prose explicitly notes a convention omitting that factor; such an unnormalized function is Γ(s+1) times the local normalized one on its convergence domain, without a separate wrapper. The polylogarithm equalities in 25.12.16 are alternative representations of these functions, not definitions of new families.

  [DLMF 25.12.E14](https://dlmf.nist.gov/25.12.E14):
  **Fermi–Dirac integral** (DLMF 25.12.14): `F_s(x) = (1/Γ(s+1)) ∫_0^∞ t^s/(e^{t-x} + 1) dt`,
  `s > -1`.
  `DLMF.Zeta.fermiDiracF` ([definition](DLMF/Zeta/Polylog.lean#L835)).

  [DLMF 25.12.E15](https://dlmf.nist.gov/25.12.E15):
  **Bose–Einstein integral** (DLMF 25.12.15): `G_s(x) = (1/Γ(s+1)) ∫_0^∞ t^s/(e^{t-x} - 1) dt`,
  for `s > -1`, `x < 0`, or `s > 0`, `x ≤ 0`.
  `DLMF.Zeta.boseEinsteinG` ([definition](DLMF/Zeta/Polylog.lean#L841)).

### §25.13 Periodic Zeta Function

- **Periodic/exponential zeta**, [25.13.1](https://dlmf.nist.gov/25.13.E1): F(x,s)=Liₛ(e²πⁱˣ). Mathlib `HurwitzZeta.expZeta (x : UnitAddCircle) s` in [HurwitzZeta](.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZeta.lean#L116) is the meromorphic continuation of exactly the exponential Dirichlet series. It is a separate upstream object, alongside the local `DLMF.Zeta.polylog` evaluated on the unit circle. Integer x and the respective series-convergence conditions require care; a totalized series outside its convergence region is not the continuation.

### §25.14 Lerch’s Transcendent

<!-- retained entry 172 -->
- **Lerch transcendent Φ(z,s,a)**, [25.14.1](https://dlmf.nist.gov/25.14.E1):
  `DLMF.Zeta.lerchPhiSeries`, `lerchPhi`, and parameter-domain predicate
  `z25b_lerchParamOK` in [Lerch](DLMF/Zeta/Lerch.lean#L44).
  The continued function chooses an analytic extension on `ℂ \ [1,∞)`;
  on the cut it retains the totalized series, which does not encode DLMF's
  two boundary values. A separate actual integral construction
  `q25b_lerchInt` and continuation predicate `q25b_IsLerchCont` occur in
  [Q25bLerchContinuation](DLMF/Zeta/Q25bLerchContinuation.lean#L124).
  Lerch's historical K notation is an exponential-argument specialization,
  without a separate local function.

<!-- retained entry 173 -->
- **Referenced polylogarithm**, [25.14.3](https://dlmf.nist.gov/25.14.E3),
  complementing [definition 25.12.10](https://dlmf.nist.gov/25.12.E10):
  `DLMF.Zeta.polylogSeriesC`, `polylog` in
  [Polylog](DLMF/Zeta/Polylog.lean#L82), and natural-order series
  `DLMF.Polylog.polylogSeries` in [Basic](DLMF/Polylog/Basic.lean#L29).
  The complex-order continuation has the same cut/fallback distinction as
  Lerch Φ; the natural-order series is not its global continuation.

- **Lerch large-argument Taylor coefficients**, [25.14.9 and prose](https://dlmf.nist.gov/25.14.E9): bₙ is the Taylor coefficient of csc(π(t−a)) at t=0. The local statement `DLMF.Zeta.hasSum_lerchPhi_neg_large` in [Lerch](DLMF/Zeta/Lerch.lean#L317) uses `iteratedDeriv n (fun t : ℂ => 1 / Complex.sin (π * (t-a))) 0 / n.factorial` inline; there is no separate public bₙ wrapper. The finite first sum is empty for nonpositive integer order m; singular integral a requires the special restrictions of the formula.

### §25.15 Dirichlet L -functions

<!-- retained entry 174 -->
- **Dirichlet L(s,χ)**, [25.15.1](https://dlmf.nist.gov/25.15.E1): Mathlib
  `DirichletCharacter.LFunction` in
  [DirichletContinuation](.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L60)
  is continued; `LSeries` applied to χ is the distinct native Dirichlet-series
  construction. Principal and nonprincipal characters have different pole behavior.

<!-- retained entry 175 -->
- **Gauss sum G(χ)**, [25.15.6](https://dlmf.nist.gov/25.15.E6):
  `DLMF.NumberTheory.gaussSumDLMF χ 1` in
  [Characters](DLMF/NumberTheory/Characters.lean#L856), and Mathlib `gaussSum`
  in [GaussSum](.lake/packages/mathlib/Mathlib/NumberTheory/GaussSum.lean).
  The latter takes multiplicative and additive characters explicitly; the
  local wrapper fixes DLMF's positive exponential convention.

### §25.16 Mathematical Applications

- **Chebyshev's prime-counting function and Euler sums**, [25.16.1](https://dlmf.nist.gov/25.16.E1), [25.16.5 and 25.16.11](https://dlmf.nist.gov/25.16.E5): ψ(x)=Σₚᵐ≤ₓlog p is Mathlib `Chebyshev.psi` in [Chebyshev](.lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean#L70), not digamma. H(s)=ΣHₙ/nˢ and H(s,z)=Σn⁻ˢΣₘ≤ₙm⁻ᶻ have no dedicated local wrapper identified; the native sums can be written with `harmonic`, finite sums and `tsum`, but the meromorphic continuation described in the prose is an additional object not supplied by an arbitrary `tsum`. These definitions occur in mathematical application notes; no new application theorem target is added.

## Chapter 26 — Combinatorial analysis

Expanded review: all 22 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§26.1–26.22 checked; matching headings are §26.2,
§26.3(i), §26.4(i), §26.5(i), §26.6(i), §26.7(i), §26.8(i), §26.9(i),
§26.10(i), §26.12(i), and §26.14(i). Tables were checked as instances of
the definitions; displayed examples do not introduce new families.

### §26.1 Special Notation

- **Rising/falling factorials and notation for signed Stirling numbers**, [26.1.1 and notation prose](https://dlmf.nist.gov/26.1.E1): the factorial polynomials are Mathlib `ascPochhammer` and `descPochhammer` in [Pochhammer](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Pochhammer.lean#L51), with evaluations at x; natural-number versions are `Nat.ascFactorial` and `Nat.descFactorial`. The bracket first-kind Stirling number [n;k] is unsigned and equals |s(n,k)|; the many alternate first-/second-kind notations listed by DLMF do not define additional sequences. DLMF's signed s requires the existing local signed wrapper, whereas Mathlib `Nat.stirlingFirst` is unsigned.

### §26.2 Basic Definitions

<!-- retained entry 176 -->
- **Permutation and cycles**, [§26.2 prose](https://dlmf.nist.gov/26.2): Mathlib
  `Equiv.Perm`, `Equiv.Perm.cycleFactorsFinset` and cycle decomposition in
  [Cycle/Factors](.lake/packages/mathlib/Mathlib/GroupTheory/Perm/Cycle/Factors.lean).
  Mathlib permits an empty underlying type, while the opening DLMF prose says
  nonempty; the empty permutation is needed by later DLMF conventions.

<!-- retained entry 177 -->
- **Planar and k-dimensional lattice paths**, [§26.2 prose](https://dlmf.nist.gov/26.2):
  `DLMF.Combinatorics.stepLists`, `latticePaths`, `unitSteps`,
  `latticePathsFin` in [Basic](DLMF/Combinatorics/Basic.lean#L59), using
  finite step lists, with `StaysWeaklyAboveDiagonal` for the ballot restriction.

<!-- retained entry 178 -->
- **Set partitions and integer partitions**, [§26.2 prose](https://dlmf.nist.gov/26.2):
  Mathlib `Finpartition` in
  [Finpartition](.lake/packages/mathlib/Mathlib/Order/Partition/Finpartition.lean)
  represents finite-set partitions, and `Nat.Partition` in
  [Partition/Basic](.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/Partition/Basic.lean)
  represents integer partitions as multisets of positive parts.

<!-- retained entry 179 -->
- **Partition number p(n)**, [§26.2 prose](https://dlmf.nist.gov/26.2):
  `DLMF.Partitions.partitionFunction` in [Partitions](DLMF/Partitions.lean#L34)
  abbreviates the cardinality of `Nat.Partition n`.

### §26.3 Lattice Paths: Binomial Coefficients

<!-- retained entry 180 -->
- **Binomial coefficient**, [26.3.1–2 and counting prose](https://dlmf.nist.gov/26.3.E1):
  Mathlib `Nat.choose`; `Finset.powersetCard` is the finite set of choices.
  Both include the zero convention when the lower index exceeds the upper.
  The local lattice-path interpretation is a theorem about `latticePaths`.

### §26.4 Lattice Paths: Multinomial Coefficients and Set Partitions

<!-- retained entry 181 -->
- **Multinomial coefficient**, [26.4.1–2](https://dlmf.nist.gov/26.4.E2):
  Mathlib `Nat.multinomial` in
  [Multinomial](.lake/packages/mathlib/Mathlib/Data/Nat/Choose/Multinomial.lean),
  and `Multiset.multinomial` when the multiplicities are stored as a multiset.
  `DLMF.Combinatorics.multisetPermutations` in
  [MultisetPermutations](DLMF/Combinatorics/MultisetPermutations.lean#L35)
  is the independently defined finite set of words with prescribed multiplicities.

<!-- retained entry 182 -->
- **Multiplicity partition λ and counts M₁,M₂,M₃**, [26.4.3–8](https://dlmf.nist.gov/26.4.E3):
  `Nat.Partition.parts` encodes λ; M₁ is `Multiset.multinomial` of its parts,
  M₂ is the cardinality of permutations of its cycle type, and M₃ is the
  corresponding set-partition count (`Multiset.bell`). These have upstream
  pointers in [MathlibCoverage](DLMF/Combinatorics/MathlibCoverage.lean#L88);
  no separate local `M1`, `M2`, or `M3` definitions are introduced.

### §26.5 Lattice Paths: Catalan Numbers

<!-- retained entry 183 -->
- **Catalan numbers**, [26.5.1](https://dlmf.nist.gov/26.5.E1): Mathlib `catalan`
  in [Catalan/Basic](.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/Catalan/Basic.lean).
  `DyckWord` in
  [DyckWord](.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/DyckWord.lean)
  gives an independent combinatorial object whose cardinality is
  the Catalan number; this is a theorem bridge, not a second scalar definition.

### §26.6 Other Lattice Path Numbers

- **Peaks of a Dyck/lattice path and Narayana's empty boundary**, [§26.6(i), 26.6.3 and Table 26.6.3](https://dlmf.nist.gov/26.6.i): a peak is an up step (0,1) followed by a right step (1,0). `DLMF.Combinatorics.c26a_numPeaks` in [LatticePaths](DLMF/Combinatorics/LatticePaths.lean#L173) counts these adjacent step pairs. The existing `narayana` uses N(n,0)=0, including N(0,0)=0; the table assigns the empty path N(0,0)=1. The positive-degree path interpretation is separate from this boundary-convention gap.

<!-- retained entry 184 -->
- **Delannoy and Motzkin numbers**, [26.6.1–2](https://dlmf.nist.gov/26.6.E1):
  `DLMF.Combinatorics.delannoy`, `motzkin` in
  [LatticePaths](DLMF/Combinatorics/LatticePaths.lean#L41), defined by recurrences;
  the path counts and displayed finite sums are theorem characterizations.

<!-- retained entry 185 -->
- **Narayana numbers**, [26.6.3](https://dlmf.nist.gov/26.6.E3):
  `DLMF.Combinatorics.narayana` in
  [LatticePaths](DLMF/Combinatorics/LatticePaths.lean#L89), with zero at k=0
  and exact natural division for the binomial formula when n>0. There is a
  boundary convention gap: [DLMF Table 26.6.3](https://dlmf.nist.gov/26.6.T3)
  has N(0,0)=1 for the empty path,
  whereas this definition gives zero. The existing path-count theorem assumes n≥1.

<!-- retained entry 186 -->
- **Large Schröder numbers**, [26.6.4](https://dlmf.nist.gov/26.6.E4): Mathlib
  `Nat.largeSchroder` in
  [Schroder](.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/Schroder.lean).

### §26.7 Set Partitions: Bell Numbers

<!-- retained entry 187 -->
- **Bell numbers**, [26.7.1–4 and partition prose](https://dlmf.nist.gov/26.7.i):
  Mathlib `Nat.bell` in [Bell](.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/Bell.lean).

- **Bell asymptotic saddle parameter**, [26.7.8](https://dlmf.nist.gov/26.7.E8): N is the positive solution of N log N=n, equivalently exp(W₀(n)), using the principal Lambert-W function from §4.13. It is expressible through the existing `DLMF.Elementary.lambertW 0` with the appropriate real/complex coercion; no separate Bell-saddle-parameter wrapper was identified. It is not the Bell number B(n).

### §26.8 Set Partitions: Stirling Numbers

<!-- retained entry 188 -->
- **Signed first-kind and second-kind Stirling numbers**,
  [§26.8(i), 26.8.1–6](https://dlmf.nist.gov/26.8.i): Mathlib
  `Nat.stirlingFirst` is **unsigned**, and `Nat.stirlingSecond` has DLMF's
  second-kind convention, in
  [Stirling](.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/Stirling.lean).
  The signed DLMF first kind is
  `DLMF.Combinatorics.signedStirlingFirst` in
  [DefinitionsAndSeries](DLMF/Combinatorics/Stirling/DefinitionsAndSeries.lean#L38).

- **Forward difference and Stirling coefficient matrices**, [26.8.32](https://dlmf.nist.gov/26.8.E32), [26.8.38](https://dlmf.nist.gov/26.8.E38): Δf(x)=f(x+1)−f(x) is Mathlib `fwdDiff 1 f`; higher differences are iterates. A=(s(j,k)) and B=(S(j,k)) are explicit finite `Matrix` expressions using the signed local Stirling function and Mathlib second-kind function. No dedicated A/B matrix wrappers are necessary. The matrix index range must include corresponding zero-degree conventions when translating the finite inverse relation.

### §26.9 Integer Partitions:
Restricted Number and Part Size

<!-- retained entry 189 -->
- **At most k parts, and boxed restrictions**,
  [§26.9(i), 26.9.1](https://dlmf.nist.gov/26.9.i):
  `DLMF.Combinatorics.partitionCountAtMostParts`, `partitionCountBoxed`
  in [RestrictedPartitions](DLMF/Combinatorics/RestrictedPartitions.lean#L49).
  The Ferrers diagram and conjugate partition are realized through Mathlib's
  Young-diagram/partition correspondence, not a separately drawn graph object.

- **Ferrers diagrams, conjugation and path area**, [§26.9(i), prose](https://dlmf.nist.gov/26.9.i): Mathlib `YoungDiagram.ofPartition` and `Nat.Partition.conjugate` in [YoungDiagram](.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/Partition/YoungDiagram.lean#L76) implement the Ferrers shape and its transpose. The boxed-partition path statistic is `DLMF.Combinatorics.latticePathArea` in [RestrictedPartitions](DLMF/Combinatorics/RestrictedPartitions.lean#L259). These are actual objects, beyond the scalar at-most/boxed partition counts. Conjugation interchanges number of parts and largest part.

- **Gaussian polynomials/q-binomial coefficients**, [26.9.4](https://dlmf.nist.gov/26.9.E4): `DLMF.QSeries.qBinom` in [QBinomial](DLMF/QSeries/Basic/Calculus.lean#L21) uses a q-Pascal recurrence and is a polynomial in q, including q=1. The displayed product quotient gives the same object in its regular domain |q|<1 with m≥n; naive termwise evaluation at q=1 would be 0/0. This is the same Gaussian coefficient notation as Chapter17, not a second restricted-partition definition.

### §26.10 Integer Partitions: Other Restrictions

<!-- retained entry 190 -->
- **Distinct, bounded distinct, odd, difference-k and Schur restrictions**,
  [§26.10(i) prose](https://dlmf.nist.gov/26.10.i):
  `DLMF.Combinatorics.partitionCountDistinct`, `partitionCountAtMostDistinct`,
  `partitionCountOdd`, `PartsDifferAtLeast`, `partitionCountDiff`,
  `SchurCondition`, `partitionCountSchur` in
  [RestrictedProducts](DLMF/Combinatorics/PartitionIdentities/RestrictedProducts.lean#L36).
  `Nat.Partition.distincts` and `odds` are the upstream finite sets underlying
  the first and third counts.

<!-- retained entry 191 -->
- **Parts drawn from S, residue set Aⱼₖ, T={2,3,…}, and combined restrictions**,
  [§26.10(i) prose](https://dlmf.nist.gov/26.10.i):
  `DLMF.Combinatorics.partitionCountIn`, `residueSetPM`, `setGeTwo`,
  `partitionCountDiffTwoNoOne`, and `partitionCountAtMostDistinctBoxed` in
  [RestrictedProducts](DLMF/Combinatorics/PartitionIdentities/RestrictedProducts.lean#L81).

- **Kloosterman sum for distinct-part partitions**, [DLMF 26.10.E18](https://dlmf.nist.gov/26.10.E18):
  (26.10.18), corrected: `A_k(n) = ∑_{1 ≤ h ≤ k, (h,k) = 1} e^{π i f(h,k) - 2π i n h/k}`.
  DLMF prints the range `1 < h ≤ k`, which gives `A_1(n) = 0` (see the module docstring).
  `DLMF.Combinatorics.distinctPartitionKloosterman` ([definition](DLMF/Combinatorics/PartitionIdentities/RogersRamanujan.lean#L321)).

- **Dedekind sum for distinct-part partitions**, [DLMF 26.10.E19](https://dlmf.nist.gov/26.10.E19):
  (26.10.19): `f(h, k) = ∑_{j=1}^k [[(2j-1)/(2k)]] [[h(2j-1)/k]]`.
  `DLMF.Combinatorics.distinctPartitionDedekindSum` ([definition](DLMF/Combinatorics/PartitionIdentities/RogersRamanujan.lean#L316)).

- **Periodic sawtooth function**, [DLMF 26.10.E20](https://dlmf.nist.gov/26.10.E20):
  (26.10.20): the sawtooth `[[x]] = x - ⌊x⌋ - 1/2` for `x ∉ ℤ`, `[[x]] = 0` for `x ∈ ℤ`.
  `DLMF.Combinatorics.sawtooth` ([definition](DLMF/Combinatorics/PartitionIdentities/RogersRamanujan.lean#L312)).

### §26.11 Integer Partitions: Compositions

- **Composition counts with length and part restrictions**, [DLMF 26.11](https://dlmf.nist.gov/26.11):
  `c(n)`: the number of compositions of `n` (DLMF §26.11).
  `DLMF.Combinatorics.compositionCount` ([definition](DLMF/Combinatorics/Compositions.lean#L36)).

  [DLMF 26.11](https://dlmf.nist.gov/26.11):
  `c_m(n)`: the number of compositions of `n` into exactly `m` parts (DLMF §26.11).
  `DLMF.Combinatorics.compositionCountLength` ([definition](DLMF/Combinatorics/Compositions.lean#L40)).

  [DLMF 26.11](https://dlmf.nist.gov/26.11):
  `c(∈ T, n)`: the number of compositions of `n` with no part `1`, `T = {2, 3, …}`
  (DLMF §26.11).
  `DLMF.Combinatorics.compositionCountNoOne` ([definition](DLMF/Combinatorics/Compositions.lean#L44)).

- **Composition objects and length/part constraints**, [§26.11](https://dlmf.nist.gov/26.11): the counts already listed are based on Mathlib `Composition n`, whose ordered positive blocks implement compositions as distinct from unordered `Nat.Partition n`. Its `.length` gives m, its `.blocks` impose the no-ones condition, and the empty composition supplies c(0)=1. Fibonacci Fₙ is Mathlib `Nat.fib`, with F₀=0,F₁=1.

### §26.12 Plane Partitions

<!-- retained entry 192 -->
- **Plane partition, box B(r,s,t), and pp(n)**,
  [§26.12(i) prose, 26.12.1–4](https://dlmf.nist.gov/26.12.i):
  `DLMF.Combinatorics.IsPlanePartition`, `planeBox`, `planePartitionsIn`,
  `planePartitionCount` in
  [BoxFormula](DLMF/Combinatorics/PlanePartitions/BoxFormula.lean#L29).
  The public construction is a finite down-closed set of positive lattice
  triples. The independent array predicate `s26b_IsPPArray` and conversions
  `s26b_toArr`, `s26b_ofArr` in the same file realize the decreasing-array definition.

- **Volume and combined symmetry classes of plane partitions**, [§26.12(i)–(ii)](https://dlmf.nist.gov/26.12.i): |π| is the cardinality of the positive-triple set, also the sum of entries of the decreasing array. Symmetric self-complementary, cyclically symmetric transpose-complement, cyclically symmetric self-complementary and totally symmetric self-complementary classes combine the already listed symmetry predicates with `planeComplement` and `planeTranspose`. They are not the same class, and no extra named predicates are needed where the local counting statements use conjunctions/equalities. `IsStrictShiftedPP`/`IsDescendingPP` use row lists, not ordinary unshifted triple sets. The box dimensions and parity restrictions are part of each enumerated subclass.

<!-- retained entry 193 -->
- **Symmetric, cyclically symmetric and totally symmetric plane partitions**,
  [prose before 26.12.5–8](https://dlmf.nist.gov/26.12.E5):
  `DLMF.Combinatorics.IsSymmetricPP`, `IsCyclicallySymmetricPP`,
  `IsTotallySymmetricPP` in
  [BoxFormula](DLMF/Combinatorics/PlanePartitions/BoxFormula.lean#L933).

<!-- retained entry 194 -->
- **Complement, self-complementary and transpose-complement conditions**,
  [prose before 26.12.9–17](https://dlmf.nist.gov/26.12.E9):
  `DLMF.Combinatorics.planeComplement`, `planeTranspose` in
  [BoxFormula](DLMF/Combinatorics/PlanePartitions/BoxFormula.lean#L946);
  the self-complementary and combined symmetry classes are equations involving
  these operations and the preceding predicates, without new named predicates.

<!-- retained entry 195 -->
- **Strict shifted and descending plane partitions**,
  [prose around 26.12.18–19](https://dlmf.nist.gov/26.12.E18):
  `DLMF.Combinatorics.IsStrictShiftedPP`, `IsDescendingPP`, and
  `DescendingPPIn` in
  [BoxFormula](DLMF/Combinatorics/PlanePartitions/BoxFormula.lean#L1089),
  using finite lists of rows rather than the unshifted triple-set representation.

### §26.13 Permutations: Cycle Notation

- **Fixed points, full cycle multiplicities, derangements and transpositions**, [§26.13, prose](https://dlmf.nist.gov/26.13): fixed points satisfy σj=j; DLMF's aⱼ counts every cycle of length j, including a₁. Mathlib `Equiv.Perm.cycleType` records nontrivial cycle lengths, so fixed points must be added separately (the partition-based local `numCycles` includes them). Mathlib `derangements` in [Basic](.lake/packages/mathlib/Mathlib/Combinatorics/Derangements/Basic.lean#L41) and `numDerangements` in [Finite](.lake/packages/mathlib/Mathlib/Combinatorics/Derangements/Finite.lean#L65) implement the object/count with no fixed points. A transposition is `Equiv.Perm.IsSwap`, built by `Equiv.swap`; an adjacent transposition is `DLMF.Combinatorics.IsAdjacentSwap` in [CyclesAndExcedances](DLMF/Combinatorics/Permutations/CyclesAndExcedances.lean#L204). Mathlib permutation sign gives ±1 and its parity.

  [DLMF 26.13](https://dlmf.nist.gov/26.13):
  The number of cycles of `σ`, fixed points included: the length of its cycle type
  `(a_1, …, a_n)` counted with multiplicity, `a_1 + ⋯ + a_n`.
  `DLMF.Combinatorics.numCycles` ([definition](DLMF/Combinatorics/Permutations/CyclesAndExcedances.lean#L47)).

### §26.14 Permutations: Order Notation

<!-- retained entry 196 -->
- **Inversion number, descents, major/greater index, Eulerian number,
  excedances and weak excedances**, [26.14.1–2 and prose](https://dlmf.nist.gov/26.14.i):
  `DLMF.Combinatorics.inversionNumber`, `wordDescentSet`, `descentNumber`,
  `majorIndex`, `eulerianNumber`, `excedanceNumber`, `weakExcedanceNumber`
  in [CyclesAndExcedances](DLMF/Combinatorics/Permutations/CyclesAndExcedances.lean#L215).
  `wordInversions` and `wordMajorIndex` are the independent word-level
  definitions underlying the permutation wrappers. `Fin n` positions are
  zero-based internally; major-index summands add one to match DLMF.

- **Descent/excedance sets and word versus permutation statistics**, [26.14.1–2 and prose](https://dlmf.nist.gov/26.14.i), [§26.16](https://dlmf.nist.gov/26.16): the project implements the descent set `wordDescentSet`, inversion count `wordInversions`, and one-based major index `wordMajorIndex`, along with the existing permutation wrappers. The same word objects apply to multiset permutations, whose equal entries do not count as inversions/descents. Weak excedance uses ≥, ordinary excedance uses >; the equality involving k+1 weak excedances has an empty-permutation boundary convention, so it should not be conflated with the definition of the Eulerian numbers at n=0.

### §26.15 Permutations: Matrix Notation

- **Rook and hit numbers for finite boards**, [DLMF 26.15](https://dlmf.nist.gov/26.15):
  `r_j(B)`: the number of ways of placing `j` nonattacking rooks on the squares of `B`
  (`r_0(B) = 1`) (DLMF §26.15).
  `DLMF.Combinatorics.rookNumber` ([definition](DLMF/Combinatorics/Permutations/RookPolynomials.lean#L77)).

  [DLMF 26.15](https://dlmf.nist.gov/26.15):
  `N_k(B)`: the number of `σ ∈ 𝔖_n` for which exactly `k` of the pairs `(j, σ(j))` lie in
  `B` (DLMF §26.15).
  `DLMF.Combinatorics.hitNumber` ([definition](DLMF/Combinatorics/Permutations/RookPolynomials.lean#L88)).

- **Permutation matrices, forbidden boards and nonattacking placements**, [26.15.1–3 and prose](https://dlmf.nist.gov/26.15.E1): Mathlib `Equiv.Perm.permMatrix` in [Permutation](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Permutation.lean#L37) puts 1 in row j, column σj, matching DLMF. A board is `Finset (Fin n × Fin n)`; nonattacking is `DLMF.Combinatorics.IsNonattacking` in [RookPolynomials](DLMF/Combinatorics/Permutations/RookPolynomials.lean#L69). Avoidance means no pair (j,σj) lies on the board, and is equivalently zero hits. The diagonal example is `diagonalBoard`; the circular ménage board is `menageBoard n` with n nonzero. These objects complement the already listed scalar rook/hit numbers and generating polynomials.

- **Rook Polynomial**, [DLMF 26.15.E3](https://dlmf.nist.gov/26.15.E3):
  (26.15.3): the rook polynomial `R(x, B) = ∑_{j=0}^n r_j(B) x^j`.
  `DLMF.Combinatorics.rookPolynomial` ([definition](DLMF/Combinatorics/Permutations/RookPolynomials.lean#L83)).

- **Board deletion and Ferrers boards**, [26.15.5](https://dlmf.nist.gov/26.15.E5), [Example2](https://dlmf.nist.gov/26.15): deletion of row j and column k is `B.filter (fun x => x.1 ≠ j ∧ x.2 ≠ k)`; deletion of one square is `B.erase (j,k)`, as in `rookPolynomial_delete`. A Ferrers board has row sizes 0≤b₁≤⋯≤bₙ and squares with k≤bⱼ; no dedicated public Ferrers-board constructor was identified. The staircase board is its specialization bⱼ=j−1. These board orientations must be distinguished from a decreasing-row Young-diagram convention.

- **Hit Polynomial**, [DLMF 26.15.E6](https://dlmf.nist.gov/26.15.E6):
  (26.15.6): `N(x, B) = ∑_{k=0}^n N_k(B) x^k`.
  `DLMF.Combinatorics.hitPolynomial` ([definition](DLMF/Combinatorics/Permutations/RookPolynomials.lean#L94)).

### §26.16 Multiset Permutations

- **Q Multinomial**, [DLMF 26.16.E1](https://dlmf.nist.gov/26.16.E1):
  (26.16.1): the `q`-multinomial coefficient
  `[a_1+⋯+a_m; a_1, …, a_m]_q = ∏_{k=1}^{m-1} [a_k + a_{k+1} + ⋯ + a_m, a_k]_q`.
  `DLMF.Combinatorics.qMultinomial` ([definition](DLMF/Combinatorics/MultisetPermutations.lean#L110)).

### §26.17 The Twelvefold Way

- **Labeling and restrictions in the twelvefold way**, [§26.17 and Table26.17.1](https://dlmf.nist.gov/26.17): the existing `DLMF.Combinatorics.twelvefoldCount` uses `Labeling` for labeled/unlabeled domain/codomain and `MapRestriction` for unrestricted/injective/surjective maps. `MapRestriction.Holds` tests the map, and `twelvefoldRel` identifies maps under relabeling when the balls/boxes are unlabeled, in [TwelvefoldWay](DLMF/Combinatorics/TwelvefoldWay.lean#L60). Thus the twelve cases count actual map equivalence classes, not twelve unrelated arithmetic definitions; empty domain/codomain cases remain explicit.

  [DLMF 26.17](https://dlmf.nist.gov/26.17):
  The entry of Table 26.17.1: the number of classes of maps `Fin n → Fin k` satisfying the
  restriction `r`, up to the permutations of the unlabeled sides (DLMF §26.17).
  `DLMF.Combinatorics.twelvefoldCount` ([definition](DLMF/Combinatorics/TwelvefoldWay.lean#L72)).

## Chapter 27 — Functions of number theory

Expanded review: all 22 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§27.1–27.22 checked; the matching heading is §27.2(i).

### §27.1 Special Notation

- **Prime/divisor/coprimality and summation conventions**, [§27.1](https://dlmf.nist.gov/27.1): primality is `Nat.Prime`, divisibility is `Dvd`, coprimality/gcd are `Nat.Coprime`/`Nat.gcd`; the chapter normally uses positive integers. Divisor sums use `Nat.divisors`, prime sums `Nat.primesLE` or the subtype of primes, and n≤x sums use floor/truncation with an explicit lower bound1. Local/upstream arithmetic functions generally assign a value at0 as well, which is additional totalization rather than a DLMF positive-domain definition.

### §27.2 Functions

<!-- retained entry 200 -->
- **Primitive root modulo n and reduced residue system**,
  [prose after 27.2.8](https://dlmf.nist.gov/27.2.i):
  `DLMF.NumberTheory.IsPrimitiveRootMod` in
  [Functions](DLMF/NumberTheory/Functions.lean#L159), using coprimality and
  `orderOf` in `ZMod n`. A reduced residue system is the corresponding
  pairwise incongruent list of units, without another local type.

<!-- retained entry 197 -->
- **Prime factorization, ν(n), ordered primes pₙ and prime-counting π(x)**,
  [27.2.1–4](https://dlmf.nist.gov/27.2.E1): Mathlib `Nat.factorization`,
  `ArithmeticFunction.cardDistinctFactors` (notation ω), `Nat.primeCounting`,
  respectively defined in
  [Factorization/Defs](.lake/packages/mathlib/Mathlib/Data/Nat/Factorization/Defs.lean),
  [ArithmeticFunction/Misc](.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Misc.lean#L324),
  [PrimeCounting](.lake/packages/mathlib/Mathlib/NumberTheory/PrimeCounting.lean);
  and `DLMF.NumberTheory.nthPrime`, `primePi` in
  [Functions](DLMF/NumberTheory/Functions.lean#L59).
  DLMF prime indices start at 1; the local index-zero value is a fallback.
  `primePi` uses the floor of a real argument, whereas the upstream counting
  function takes a natural number.

<!-- retained entry 198 -->
- **Unit arithmetic function**, [27.2.5](https://dlmf.nist.gov/27.2.E5):
  the identity `1 : ArithmeticFunction R` in
  [Defs](.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean),
  with value one at n=1 and zero otherwise. DLMF considers positive n.

<!-- retained entry 199 -->
- **Totient power sums and Euler totient**, [27.2.6–7](https://dlmf.nist.gov/27.2.E6):
  `DLMF.NumberTheory.totientPowerSum` in
  [Functions](DLMF/NumberTheory/Functions.lean#L135), and Mathlib `Nat.totient`
  in [Totient](.lake/packages/mathlib/Mathlib/Data/Nat/Totient.lean).

<!-- retained entry 201 -->
- **Divisor d and ordered-factor dₖ**, [27.2.9](https://dlmf.nist.gov/27.2.E9):
  Mathlib `ArithmeticFunction.sigma 0` and
  `DLMF.NumberTheory.divisorCountK` in
  [Functions](DLMF/NumberTheory/Functions.lean#L195).

<!-- retained entry 202 -->
- **Divisor power sum σα**, [27.2.10](https://dlmf.nist.gov/27.2.E10):
  Mathlib `ArithmeticFunction.sigma` in
  [ArithmeticFunction/Misc](.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Misc.lean#L143)
  for natural exponents, and complex-exponent
  `DLMF.NumberTheory.sigmaC`, with `powC`, in
  [Functions](DLMF/NumberTheory/Functions.lean#L213).

<!-- retained entry 203 -->
- **Jordan Jₖ**, [27.2.11](https://dlmf.nist.gov/27.2.E11):
  `DLMF.NumberTheory.jordanTotient` in
  [Functions](DLMF/NumberTheory/Functions.lean#L257), an actual finite tuple count.

<!-- retained entry 204 -->
- **Möbius μ, Liouville λ and von Mangoldt Λ**, [27.2.12–14](https://dlmf.nist.gov/27.2.E12):
  Mathlib `ArithmeticFunction.moebius`, `liouville`, `vonMangoldt` in
  [Moebius](.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean),
  [Liouville](.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Liouville.lean),
  [VonMangoldt](.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean).

### §27.3 Multiplicative Properties

- **Multiplicative arithmetic-function predicate**, [DLMF 27.3.E1](https://dlmf.nist.gov/27.3.E1):
  DLMF 27.3.1: `f` is multiplicative on the positive integers if `f(1) = 1` and
  `f(mn) = f(m)f(n)` whenever `(m, n) = 1`.
  `DLMF.NumberTheory.IsMultiplicativeFn` ([definition](DLMF/NumberTheory/Functions.lean#L333)).

- **Arithmetic-function structures and multiplicativity**, [27.3.1 and 27.3.9](https://dlmf.nist.gov/27.3.E1): in addition to the local positive-domain predicates, Mathlib `ArithmeticFunction` and `ArithmeticFunction.IsMultiplicative` in [Defs](.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean#L423) package the zero-at0 convention and coprime multiplicativity. Complete multiplicativity can be represented by a multiplicative homomorphism on the relevant domain. These structured objects are distinct from unconstrained functions ℕ→ℂ; values at0 must be matched before adopting an upstream instance.

- **Completely multiplicative arithmetic-function predicate**, [DLMF 27.3.E9](https://dlmf.nist.gov/27.3.E9):
  DLMF 27.3.9: `f` is completely multiplicative if `f(1) = 1` and `f(mn) = f(m)f(n)` for
  all `m, n = 1, 2, …`.
  `DLMF.NumberTheory.IsCompletelyMultiplicativeFn` ([definition](DLMF/NumberTheory/Functions.lean#L350)).

### §27.4 Euler Products and Dirichlet Series

- **Euler product and Dirichlet generating function**, [27.4.1–4](https://dlmf.nist.gov/27.4.E1): the Euler product has prime-local factors 1+Σᵣ≥₁f(pʳ), or (1−f(p))⁻¹ in the completely multiplicative case; it is a `tprod` over primes under absolute convergence. The generating function F(s)=Σf(n)n⁻ˢ is Mathlib `LSeries f s`, a native totalized Dirichlet series, not a meromorphic continuation by definition. Prime-factor terms and convergence conditions are part of the mathematical meaning, not additional named special-function wrappers.

### §27.5 Inversion Formulas

- **Dirichlet convolution and its unit/inverse**, [27.5.1 and prose](https://dlmf.nist.gov/27.5.E1): h(n)=Σd|nf(d)g(n/d) is multiplication in Mathlib `ArithmeticFunction`; its identity is the arithmetic delta function at 1. Functions with nonzero f(1) over a field give units for this convolution algebra. This is a different product from pointwise multiplication of functions, and DLMF's value-at0 omission must be supplied when passing to `ArithmeticFunction`. Möbius inversion supplies the inverse for divisor summation, without defining a second Möbius function.

### §27.7 Lambert Series as Generating Functions

- **Lambert Series**, [DLMF 27.7.E1](https://dlmf.nist.gov/27.7.E1):
  DLMF 27.7.1: the Lambert series `∑_{n≥1} f(n) xⁿ/(1 - xⁿ)` (a totalized `tsum`; the
  statements below assert convergence).
  `DLMF.NumberTheory.lambertSeries` ([definition](DLMF/NumberTheory/DivisorSums.lean#L284)).

### §27.8 Dirichlet Characters

- **Native Dirichlet characters, principal/conjugate/real characters**, [§27.8](https://dlmf.nist.gov/27.8): Mathlib `DirichletCharacter ℂ k` is the structured finite-residue character behind the local `IsDirichletCharacterFn` predicate. The principal character is `1 : DirichletCharacter ℂ k`, conjugation is complex conjugation of its values, and a real character has zero imaginary part at every residue. Primitive and induced-modulus predicates are already catalogued; the native conductor/primitive-character APIs give a second structured realization. There is no separate local real-character predicate or enumeration χ₁,…,χφ(k).

  [DLMF 27.8.E1](https://dlmf.nist.gov/27.8.E1):
  DLMF 27.8.1–27.8.4: `χ` is a Dirichlet character mod `k` if `χ(1) = 1`,
  `χ(mn) = χ(m)χ(n)`, `χ(n + k) = χ(n)` (`m, n = 1, 2, …`) and `χ(n) = 0` when `(n, k) > 1`.
  `DLMF.NumberTheory.IsDirichletCharacterFn` ([definition](DLMF/NumberTheory/Characters.lean#L42)).

- **Primitive Dirichlet-character predicate**, [DLMF 27.8](https://dlmf.nist.gov/27.8#p4):
  §27.8 after 27.8.6: DLMF's definition of a primitive character mod `k`: for every divisor
  `d < k` of `k` there is `a ≡ 1 (mod d)` with `(a, k) = 1` and `χ(a) ≠ 1`.
  `DLMF.NumberTheory.IsPrimitiveDLMF` ([definition](DLMF/NumberTheory/Characters.lean#L186)).

- **Inducing-modulus predicate for Dirichlet characters**, [DLMF 27.8.E7](https://dlmf.nist.gov/27.8.E7):
  DLMF 27.8.7: a divisor `d` of `k` is an induced modulus for `χ` if `χ(a) = 1` for all
  `a ≡ 1 (mod d)` with `(a, k) = 1`.
  `DLMF.NumberTheory.IsInducedModulus` ([definition](DLMF/NumberTheory/Characters.lean#L260)).

### §27.9 Quadratic Characters

- **Legendre and Jacobi symbols/quadratic characters**, [§27.9](https://dlmf.nist.gov/27.9): Mathlib `legendreSym p n` in [Basic](.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/Basic.lean#L109) has modulus p first, while DLMF writes (n|p); Mathlib `jacobiSym n P` in [JacobiSymbol](.lake/packages/mathlib/Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean#L86) has numerator first. Values are integers0,±1, with (n|1)=1. Their multiplicative-character interpretations require the stated odd-prime/positive-odd-modulus regimes; Jacobi value1 alone does not assert a square modulo a composite modulus.

### §27.10 Periodic Number-Theoretic Functions

- **Periodic arithmetic-function predicate**, [DLMF 27.10.E1](https://dlmf.nist.gov/27.10.E1):
  DLMF 27.10.1: `f` is periodic mod `k` if `f(n + k) = f(n)`, `n = 1, 2, …`.
  `DLMF.NumberTheory.IsPeriodicFn` ([definition](DLMF/NumberTheory/Characters.lean#L423)).

- **Finite Fourier coefficients**, [DLMF 27.10.E3](https://dlmf.nist.gov/27.10.E3):
  DLMF 27.10.3: the finite Fourier coefficients `g(m) = k⁻¹ ∑_{n=1}^k f(n) e^{-2πimn/k}`.
  `DLMF.NumberTheory.finiteFourierCoeff` ([definition](DLMF/NumberTheory/Characters.lean#L438)).

- **Ramanujan Sum**, [DLMF 27.10.E4](https://dlmf.nist.gov/27.10.E4):
  DLMF 27.10.4: Ramanujan's sum `c_k(n) = ∑_{m=1}^k χ₁(m) e^{2πimn/k}`, the sum over
  `1 ≤ m ≤ k` with `(m, k) = 1`.
  `DLMF.NumberTheory.ramanujanSum` ([definition](DLMF/NumberTheory/Characters.lean#L665)).

- **Divisor Convolution Sum**, [DLMF 27.10.E6](https://dlmf.nist.gov/27.10.E6):
  DLMF 27.10.6: `s_k(n) = ∑_{d∣(n,k)} f(d) g(k/d)`.
  `DLMF.NumberTheory.divisorConvolutionSum` ([definition](DLMF/NumberTheory/Characters.lean#L762)).

- **Fourier kernel and generalized Ramanujan coefficients**, [27.10.2–3 and 27.10.8](https://dlmf.nist.gov/27.10.E8): `DLMF.NumberTheory.expFrac` in [Characters](DLMF/NumberTheory/Characters.lean#L435) is exp(2πimn/k). The finite transform `finiteFourierCoeff` uses the negative exponential and the factor1/k. The aₖ(m) in the generalized divisor-convolution expansion is the displayed divisor sum Σd|(m,k)g(d)f(k/d)d/k; no separate public a-wrapper was found. `GaussSumSeparable` tests the exact normalization G(n,χ)=conj(χ(n))G(1,χ), not separability of a polynomial or field extension.

  [DLMF 27.10.E10](https://dlmf.nist.gov/27.10.E10):
  DLMF 27.10.10: `G(n, χ)` is separable for `n` if `G(n, χ) = χ̄(n) G(1, χ)`.
  `DLMF.NumberTheory.GaussSumSeparable` ([definition](DLMF/NumberTheory/Characters.lean#L889)).

- **Gauss sum in the DLMF normalization**, [DLMF 27.10.E9](https://dlmf.nist.gov/27.10.E9):
  DLMF 27.10.9: the Gauss sum `G(n, χ) = ∑_{m=1}^k χ(m) e^{2πimn/k}`.
  `DLMF.NumberTheory.gaussSumDLMF` ([definition](DLMF/NumberTheory/Characters.lean#L856)).

### §27.11 Asymptotic Formulas: Partial Sums

- **Divisor-problem exponent and constants in prime sums**, [§27.11 prose and 27.11.8–9](https://dlmf.nist.gov/27.11): θ₀ is the infimum exponent such that the divisor summatory error is O(xᶿ) for every θ>θ₀; A and B(h,k) denote constant terms in reciprocal-prime asymptotics. No dedicated local θ₀/A/B objects were identified. Helper constants bounding a remainder are not definitions of these asymptotic constants. The count of primes in an arithmetic progression is an explicit filtered prime count, not a second ordinary π(x).

- **Partial-sum asymptotic predicate**, [DLMF 27.11.E1](https://dlmf.nist.gov/27.11.E1):
  DLMF 27.11.1: the asymptotic formula `∑_{n≤x} f(n) = F(x) + O(g(x))` as `x → ∞`.
  `DLMF.NumberTheory.HasPartialSumAsymptotic` ([definition](DLMF/NumberTheory/Asymptotics/DivisorSums.lean#L32)).

### §27.12 Asymptotic Formulas: Primes

- **Mersenne/Fermat numbers, probable primes and Carmichael numbers**, [§27.12 prose](https://dlmf.nist.gov/27.12), [§27.18](https://dlmf.nist.gov/27.18): Mathlib `mersenne p` in [LucasLehmer](.lake/packages/mathlib/Mathlib/NumberTheory/LucasLehmer.lean#L39) is2ᵖ−1, and `Nat.fermatNumber n` in [Fermat](.lake/packages/mathlib/Mathlib/NumberTheory/Fermat.lean#L35) is2^(2ⁿ)+1. Mersenne primality is a primality condition on that number. Mathlib `Nat.ProbablePrime`/`Nat.FermatPsp` in [FermatPsp](.lake/packages/mathlib/Mathlib/NumberTheory/FermatPsp.lean#L54) distinguish the base-b congruence from compositeness; `Nat.IsCarmichael` in [CarmichaelNumber](.lake/packages/mathlib/Mathlib/NumberTheory/CarmichaelNumber.lean#L48) packages the composite/all-base condition. The all-base and coprime-base conditions in these predicates have their respective stated conventions. Record-size and timing statements are excluded as numerical/computational examples.

### §27.13 Functions

- **Restricted additive representation counts, Goldbach pairs and square-divisor classes**, [§27.13(i)–(ii)](https://dlmf.nist.gov/27.13.i), [27.13.6–7](https://dlmf.nist.gov/27.13.E6): S(n) is a generic count of representations by elements of a prescribed set; in Goldbach it counts solutions n=p+q with odd primes. No dedicated general S/Goldbach-pair count wrapper was identified; the existing conjecture asserts existence. For square representations the existing `sumSquaresCount` counts ordered signed integer tuples, unlike unordered partitions. δ₁(n),δ₃(n) are the numbers of divisors congruent to1,3 mod4, explicit filtered divisor counts with no standalone local functions. The existing `jacobiThetaSeries` is the q/nome theta series, not a θ-function evaluated with q mistaken for a period ratio.

  [DLMF 27.13.E3](https://dlmf.nist.gov/27.13.E3):
  DLMF 27.13.3: `r_k(n)`, the number of solutions of `n = x₁² + ⋯ + x_k²` in integers
  (positive, negative or zero, order taken into account).
  `DLMF.NumberTheory.sumSquaresCount` ([definition](DLMF/NumberTheory/Additive.lean#L186)).

  [DLMF 27.13.E4](https://dlmf.nist.gov/27.13.E4):
  DLMF 27.13.4: `ϑ(x) = 1 + 2 ∑_{m≥1} x^{m²}`, `|x| < 1` (a totalized `tsum`).
  `DLMF.NumberTheory.jacobiThetaSeries` ([definition](DLMF/NumberTheory/Additive.lean#L193)).

- **Goldbach Conjecture**, [DLMF 27.13.ii](https://dlmf.nist.gov/27.13.ii):
  §27.13(ii): Goldbach's conjecture, every even integer `n > 4` is the sum of two odd primes
  (an open problem; stated as a proposition only).
  `DLMF.NumberTheory.GoldbachConjecture` ([definition](DLMF/NumberTheory/Additive.lean#L40)).

- **Hardy Littlewood Waring Conjecture**, [DLMF 27.13.iii](https://dlmf.nist.gov/27.13.iii):
  §27.13(iii): the Hardy–Littlewood conjectures `G(k) < 2k + 1` for `k` not a power of `2`
  and `G(k) ≤ 4k` for `k` a power of `2` (open; stated as a proposition only).
  `DLMF.NumberTheory.HardyLittlewoodWaringConjecture` ([definition](DLMF/NumberTheory/Additive.lean#L172)).

- **Waring representations and Waring numbers**, [DLMF 27.13.E1](https://dlmf.nist.gov/27.13.E1):
  DLMF 27.13.1: every `n ≥ 1` is a sum `x₁^k + ⋯ + x_m^k` of `m` `k`th powers of
  nonnegative integers.
  `DLMF.NumberTheory.IsWaringNumber` ([definition](DLMF/NumberTheory/Additive.lean#L63)).

  [DLMF 27.13.E1](https://dlmf.nist.gov/27.13.E1):
  §27.13(iii): `g(k)`, the smallest `m` for which 27.13.1 is solvable for all `n ≥ 1`.
  `DLMF.NumberTheory.waringSmallG` ([definition](DLMF/NumberTheory/Additive.lean#L69)).

  [DLMF 27.13.E1](https://dlmf.nist.gov/27.13.E1):
  §27.13(iii): `G(k)`, the smallest `m` for which 27.13.1 is solvable for all sufficiently
  large `n`.
  `DLMF.NumberTheory.waringBigG` ([definition](DLMF/NumberTheory/Additive.lean#L73)).

### §27.14 Unrestricted Partitions

- **Partition functions across Chapters26–27 and signed-index conventions**, [§27.14(i)–(ii)](https://dlmf.nist.gov/27.14.i): p(n) is the already catalogued `DLMF.Partitions.partitionFunction`; `DLMF.NumberTheory.partitionsAtMost` and `DLMF.Combinatorics.partitionCountAtMostParts` separately realize the same at-most-k count as finite cardinalities. DLMF extends p(k)=0 for negative k in 27.14.6, whereas these functions have natural indices; a guarded integer-to-natural conversion is necessary when translating the recurrence. The Euler product `eulerReciprocal` is f itself, not1/f despite its name; it equals `(x;x)∞`.

  [DLMF 27.14.i](https://dlmf.nist.gov/27.14.i):
  §27.14(i): `p_k(n)`, the number of partitions of `n` into at most `k` parts.
  `DLMF.NumberTheory.partitionsAtMost` ([definition](DLMF/NumberTheory/Partitions.lean#L361)).

  [DLMF 27.14.E2](https://dlmf.nist.gov/27.14.E2):
  DLMF 27.14.2: Euler's reciprocal function `f(x) = ∏_{m≥1} (1 - xᵐ)`, `|x| < 1`
  (a totalized `tprod`).
  `DLMF.NumberTheory.eulerReciprocal` ([definition](DLMF/NumberTheory/Partitions.lean#L368)).

- **Generalized pentagonal numbers, Hardy–Ramanujan scale and Dedekind sums**, [27.14.5](https://dlmf.nist.gov/27.14.E5), [27.14.8–11](https://dlmf.nist.gov/27.14.E8): Mathlib `pentagonal : ℤ → ℕ` gives ω(k)=(3k²−k)/2, with both signs of k. K=π√(2/3) is an unnamed elementary constant. `DLMF.Weierstrass.dedekindSum` in [ModularFunctions](DLMF/Weierstrass/ModularFunctions.lean#L751) is the exact s(h,k) used in `DLMF.NumberTheory.rademacherA`; it is a different shifted sum from `DLMF.Combinatorics.distinctPartitionDedekindSum` in 26.10.19. The Rademacher summand uses the derivative of sinh(K√t/k)/√t at t=n−1/24, not another independently normalized partition function.

  [DLMF 27.14.E10](https://dlmf.nist.gov/27.14.E10):
  DLMF 27.14.10: `A_k(n) = ∑_{1≤h≤k, (h,k)=1} exp(πi s(h, k) - 2πi n h/k)`.
  `DLMF.NumberTheory.rademacherA` ([definition](DLMF/NumberTheory/Partitions.lean#L483)).

- **Dedekind eta, multiplier and normalized discriminant**, [27.14.12–16](https://dlmf.nist.gov/27.14.E12): Mathlib `ModularForm.eta` in [DedekindEta](.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/DedekindEta.lean#L57) supplies η(τ) with Imτ>0; the project's eta notation refers to this function. The multiplier ε=exp(πi((a+d)/(12c)−s(d,c))) is explicit in the transformation formula, not a separately named wrapper. `discriminantDLMF` includes (2π)¹² times η²⁴, so it differs from the often normalized modular discriminant η²⁴. `ramanujanTau` is defined by a formal integer power-series product, separately from the analytic eta product; the generating-function bridge should not erase this normalization.

  [DLMF 27.14.E16](https://dlmf.nist.gov/27.14.E16):
  DLMF 27.14.16: the discriminant `Δ(τ) = (2π)¹² η(τ)²⁴`, `ℑτ > 0`.
  `DLMF.NumberTheory.discriminantDLMF` ([definition](DLMF/NumberTheory/Partitions.lean#L557)).

  [DLMF 27.14.E18](https://dlmf.nist.gov/27.14.E18):
  DLMF 27.14.18: Ramanujan's `τ(n)`, the `n`th coefficient of `x ∏_{m≥1} (1 - xᵐ)²⁴`.
  `DLMF.NumberTheory.ramanujanTau` ([definition](DLMF/NumberTheory/Partitions.lean#L580)).

- **Lehmer Conjecture**, [DLMF 27.14.vi](https://dlmf.nist.gov/27.14.vi):
  §27.14(vi): Lehmer's conjecture `τ(n) ≠ 0` for `n ≥ 1` (open; stated as a proposition
  only).
  `DLMF.NumberTheory.LehmerConjecture` ([definition](DLMF/NumberTheory/Partitions.lean#L723)).

### §27.15 Chinese Remainder Theorem

- **Chinese-remainder residue representation**, [§27.15](https://dlmf.nist.gov/27.15): for pairwise coprime moduli the tuple of residues is represented by a product of `ZMod mᵢ`, with the Chinese-remainder equivalence to residues modulo Πmᵢ. These are standard Mathlib quotient/congruence constructions; no new DLMF-specific residue-number-system type is defined. The numerical digit-length/timing example is excluded; it introduces no additional number-theoretic function.

### §27.16 Cryptography

- **Public-key coding residue maps**, [§27.16](https://dlmf.nist.gov/27.16): the application defines n=pq, a public exponent r, inverse exponent s modulo φ(n), encryption x↦xʳ modn and decryption y↦yˢ modn. These are exponentiation and inverses in modular arithmetic, with no dedicated local cryptographic interface identified. They are application-note definitions excluded from new acquisition targets; the dated security/timing and decimal-size examples are not mathematical coverage claims.

## Chapter 28 — Mathieu functions and Hill's equation

Expanded review: all 36 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§28.1–28.36 checked; matching headings are §§28.2,
28.4(i), 28.5(i), 28.12, 28.20 and 28.29.

Names in this chapter are in `DLMF.Mathieu`.

### §28.1 Special Notation

- **Alternative Mathieu parameters and historical normalizations**, [§28.1](https://dlmf.nist.gov/28.1): DLMF uses `q = h²`. Other sources replace `a` by `λ` or use `8q` in the position of DLMF's `q`. Campbell's `inₙ, jnₙ, cehₙ, sehₙ, inhₙ, jnhₙ` are respectively `feₙ, geₙ, Ceₙ, Seₙ, Feₙ, Geₙ`; Abramowitz–Stegun's `Fν` is `Meν`. The NBS and Stratton `Seₙ, Soₙ` are instead `ceₙ(z,q)/ceₙ(0,q)` and `seₙ(z,q)/seₙ′(0,q)`, with parameters `s=4q` and `c=2√q`, respectively. Thus their `Seₙ` is not the modified function `DLMF.Mathieu.modMathieuSe`. The Arscott–McLachlan `Fey, Gey, Me⁽¹,²⁾, Ne⁽¹,²⁾` are the displayed scalar multiples of the radial functions using joining factors and values at zero. Existing angular, modified, radial and joining-factor objects express these aliases; there are no additional public wrappers for the historical notation.

### §28.2 Definitions and Basic Properties

<!-- retained entry 205 -->
- **Mathieu equation and normalized fundamental solutions wᵢ, wᵢᵢ**,
  [28.2.1 and 28.2.5](https://dlmf.nist.gov/28.2.E1):
  `IsMathieuSolution`, `mathieuWI`, `mathieuWII` in
  [Basic](DLMF/Mathieu/Basic/EquationAndSolutions.lean#L42). The functions are chosen from entire
  initial-value solutions, with zero fallback if existence fails; existence
  is proved by `exists_isMathieuSolution` in that file. The algebraic
  coordinate forms 28.2.2–3 are equation transformations, not separately
  defined functions.

<!-- retained entry 206 -->
- **Floquet solution, characteristic exponent and monodromy matrix**,
  [28.2.14–16](https://dlmf.nist.gov/28.2.E14): `IsFloquetSolution`,
  `IsMathieuCharExp`, `mathieuMonodromy` in
  [Basic](DLMF/Mathieu/Basic/EquationAndSolutions.lean#L67). The exponent predicate permits the
  full ambiguity ±ν+2n. DLMF's principal exponent, specified in the prose
  following 28.2.16 using the inverse cosine, has no separate selected Lean
  object. Bilateral-series coefficients are recorded under §28.12 below.

- **Principal representative of the characteristic exponent**, [28.2.16](https://dlmf.nist.gov/28.2.E16): `ν̂ = arccos(wᵢ(π;a,q))/π`, while the complete exponent set is `±ν̂+2n`, `n∈ℤ`. `DLMF.Mathieu.IsMathieuCharExp` records the characteristic-exponent relation, rather than choosing this principal representative. No dedicated public `ν̂` function was identified. The real-parameter spectral choices `DLMF.Mathieu.mathieuA` and `DLMF.Mathieu.mathieuB` should not be read as a choice of every complex-parameter branch; §28.7 discusses their branch points and continuation.

<!-- retained entry 207 -->
- **Characteristic values aₙ(q), bₙ(q)**,
  [Table 28.2.1 and 28.2.23–24](https://dlmf.nist.gov/28.2.T1):
  `mathieuSpecA`, `mathieuSpecB`, `mathieuA`, `mathieuB`, with the ordering
  helper `nthLeast`, in [Basic](DLMF/Mathieu/Basic/Spectral.lean#L29).
  These take real q; the complex-q continuation discussed by DLMF is not a
  second defined a/b family. The spectra are boundary-value sets and their
  selected values use the parity-dependent indices n/2 and (n−1)/2;
  `mathieuB 0` is a fallback. Their nonempty ordered characterization is
  proved by `mathieuSpecA_exists` and `mathieuSpecB_exists` in the same file.

<!-- retained entry 208 -->
- **Periodic Mathieu functions ceₙ, seₙ**,
  [Table 28.2.2 and 28.2.29–30](https://dlmf.nist.gov/28.2.T2):
  `mathieuCe`, `mathieuSe`, with `mathieuCeZero`, `mathieuSeDerivZero`, in
  [Basic](DLMF/Mathieu/Basic/Functions.lean#L23). These are normalized multiples of
  wᵢ and wᵢᵢ for real q and complex z, using a positive square root of the
  squared norm integral. They are distinct from the noninteger-order
  symmetrizations below.

### §28.4 Fourier Series

<!-- retained entry 209 -->
- **Fourier coefficients Aₘⁿ(q), Bₘⁿ(q)**,
  [28.4.1–4](https://dlmf.nist.gov/28.4.E1): `mathieuFourierA`,
  `mathieuFourierB` in [Basic](DLMF/Mathieu/Basic/Functions.lean#L118), defined by
  integrals of ceₙ and seₙ. The m=0 cosine coefficient has the additional
  factor 1/2; the same functions handle all four parity families.

- **Fourier-coefficient indexing and complex normalization**, [28.4.1–4](https://dlmf.nist.gov/28.4.E1) and [28.14.4–5](https://dlmf.nist.gov/28.14.E4): `DLMF.Mathieu.mathieuFourierA` and `DLMF.Mathieu.mathieuFourierB` take the actual nonnegative harmonic index, with the constant cosine coefficient carrying the usual half factor. `DLMF.Mathieu.mathieuMeCoeff ν q m` uses the half-index `m∈ℤ` for DLMF's `c₂ₘν`. The additional predicate `DLMF.Mathieu.IsMeCoeffSeq` in [Noninteger/Defs](DLMF/Mathieu/Noninteger/Basic.lean#L69) imposes the three-term recurrence, absolute summability and `HasSum (fun m => c m ^ 2) 1`. The last normalization is a sum of squares, not a sum of squared complex norms.

### §28.5 Second Solutions fe n , ge n

<!-- retained entry 210 -->
- **Second solutions feₙ, geₙ, periodic parts fₙ, gₙ and factors Cₙ, Sₙ**,
  [28.5.1–7](https://dlmf.nist.gov/28.5.E1): `mathieuFe`, `mathieuGe`,
  `mathieuFeF`, `mathieuGeG`, `mathieuFeC`, `mathieuGeS` in
  [Basic](DLMF/Mathieu/Basic/Functions.lean#L77). The construction also exposes
  `mathieuFeMu`, `mathieuFeU`, `mathieuGeMu`, `mathieuGeU`,
  `mathieuFeDerivZero`, `mathieuGeZero` in
  [Basic](DLMF/Mathieu/Basic/Functions.lean#L51). These use real q and normalized
  fundamental solutions. fe₀(z,0)=z is explicit; dividing by a vanishing
  Cₙ or Sₙ in the periodic-part definitions is totalized and does not define
  the limiting periodic parts at those exceptional parameters.

### §28.6 Expansions for Small q

- **Finite continued-fraction approximants**, [28.6.16–19](https://dlmf.nist.gov/28.6.E16) and [28.15.2](https://dlmf.nist.gov/28.15.E2): `DLMF.Mathieu.mathieuCFHead` and `DLMF.Mathieu.mathieuCFTail` in [ContFracDefs](DLMF/Mathieu/Basic/ContinuedFractions.lean#L30) encode the finite head and tail fractions used for integer characteristic values. `DLMF.Mathieu.mathieuContFrac` in [Noninteger/Defs](DLMF/Mathieu/Noninteger/Basic.lean#L196) encodes the finite truncation with denominators `a-(ν+2k)²`. These are finite totalized rational expressions; an infinite continued fraction is represented separately by a convergence statement about the truncations.

- **Radii of convergence ρₙ⁽ʲ⁾ and the elliptic comparison constant**, [28.6.20](https://dlmf.nist.gov/28.6.E20): `ρₙ⁽ʲ⁾` are the radii for the indicated small-`q` characteristic-value series. The exact constant is `k k′ K(k)²`, where `0<k<1`, `2E(k)=K(k)` and `k′=√(1-k²)`. Existing objects are `DLMF.EllipticIntegrals.compEllIntEk` and `DLMF.JacobiElliptic.compEllIntKk`; there is no separate public radius sequence or selected root `k`. The local theorem `DLMF.Mathieu.mathieu_radius_liminf` expresses the result through existence of analytic extensions to growing discs, rather than defining `ρₙ⁽ʲ⁾`. The decimal constant and Table 28.6.1 are excluded: numerical.

### §28.8 Asymptotic Expansions for Large q

- **Sips' scaled variable and auxiliary functions**, [§28.8(ii), 28.8.3–7](https://dlmf.nist.gov/28.8.ii): with `h=√q`, `s=2m+1` and `ξ=2√h cos x`, DLMF sets `Dₘ(ξ)=exp(-ξ²/4) Heₘ(ξ)` and introduces `Uₘ,Vₘ,Ĉₘ,Ŝₘ` in the displayed decomposition and asymptotic expansions. Mathlib's probabilists' Hermite polynomial is `Polynomial.hermite`, defined in [Hermite/Basic](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Hermite/Basic.lean#L48), so the explicit `Dₘ` expression uses that polynomial after coefficient coercion. No separate public local definitions of these Sips auxiliary families were identified. The exact asymptotic coefficient formulas are within scope.

- **Goldstein's angular auxiliary functions**, [§28.8(iii), 28.8.8–12](https://dlmf.nist.gov/28.8.iii): `Wₘ⁺,Wₘ⁻` are the explicit exponential and half-angle factors in 28.8.9; `Pₘ,Qₘ,σₘ,τₘ₊₁` are the coefficient functions and normalizing factors in the angular expansion. No dedicated public definitions for these families were identified. They should not be conflated with `DLMF.Mathieu.goldsteinFc`, `DLMF.Mathieu.goldsteinGc`, `DLMF.Mathieu.goldsteinFs`, and `DLMF.Mathieu.goldsteinGs`, which implement the different modified-function expansions of §28.26.

### §28.11 Expansions in Series of Mathieu Functions

- **Periodic Mathieu expansion coefficients αₙ, βₙ**, [28.11.1–2](https://dlmf.nist.gov/28.11.E2): these are `(1/π)∫₀²π f(x)ceₙ(x,q) dx` and `(1/π)∫₀²π f(x)seₙ(x,q) dx`. The local expansion statements in [Expansions](DLMF/Mathieu/Expansions.lean) use the integrals inline; no separate public coefficient maps were identified.

### §28.12 Definitions and Basic Properties

<!-- retained entry 211 -->
- **Noninteger characteristic value λν(q) and normal parameter values**,
  [§28.12(i), including 28.12.1–3](https://dlmf.nist.gov/28.12.i):
  `IsMathieuLambdaPath`, `MathieuNormalSegment`, `mathieuLambdaData`,
  `mathieuLambda`, `mathieuLambdaInt` in
  [Noninteger/Defs](DLMF/Mathieu/Noninteger/Basic.lean#L77).
  The selected analytic continuation follows the straight segment from 0
  to q and requires a unique endpoint, starting at ν². This is a particular
  path/domain implementation of DLMF's continuation, not a globally
  single-valued continuation across exceptional points. Integer ν is
  handled through a/b only for real q, with a zero fallback otherwise.
  The existence statement for real noninteger ν and real q,
  `mathieuNormalSegment_real`, remains admitted in
  [Properties](DLMF/Mathieu/Noninteger/Properties.lean#L250).

<!-- retained entry 212 -->
- **Floquet eigenfunction meν and coefficients c₂ₙν**,
  [28.12.4–5 and 28.12.11](https://dlmf.nist.gov/28.12.E4):
  `mathieuMe`, `mathieuMeCoeff`, `mathieuMeInt` in
  [Noninteger/Defs](DLMF/Mathieu/Noninteger/Basic.lean#L111).
  Noninteger functions use the chosen bilateral Fourier series with c₀(0)=1;
  integer orders use the separately specified √2 ceₙ or −√2 i seₙ
  normalization. Their noninteger characterization has the continuation
  qualification above.

- **Integer conventions for the bilateral Floquet family**, [28.12.11](https://dlmf.nist.gov/28.12.E11): `DLMF.Mathieu.mathieuMeInt` uses `meₙ=√2 ceₙ` for nonnegative `n` and `me₋ₙ=-√2 i seₙ` for positive `n`. These are assigned integer-order normalizations, not a claim that the noninteger continuation has these limits as the order approaches an integer. The related integer characteristic-value choice uses the real-`q` angular spectrum, with a fallback outside its selected domain. For noninteger order, `DLMF.Mathieu.IsMathieuLambdaPath` and `DLMF.Mathieu.MathieuNormalSegment` track continuation along the segment from `0` to `q`; they do not select all sheets of the global complex continuation.

<!-- retained entry 213 -->
- **Noninteger ceν, seν**, [28.12.12–13](https://dlmf.nist.gov/28.12.E12):
  `mathieuCeNu`, `mathieuSeNu` in
  [Noninteger/Defs](DLMF/Mathieu/Noninteger/Basic.lean#L151), the even and odd
  symmetrizations of meν. These are actual additional objects, rather than
  aliases for the integer-order `mathieuCe` and `mathieuSe` families.

### §28.17 Stability as x → ± ∞

- **Mathieu stability predicate**, [DLMF 28.17](https://dlmf.nist.gov/28.17):
  The pair `(a, q)` is **stable** (DLMF §28.17): all solutions of Mathieu's equation 28.2.1
  are bounded on the real axis. Otherwise the pair is unstable.
  `DLMF.Mathieu.IsMathieuStable` ([definition](DLMF/Mathieu/Noninteger/Basic.lean#L205)).

### §28.19 Expansions in Series of me ν + 2 ⁢ n Functions

- **Noninteger Floquet expansion coefficient fₙ**, [28.19.2–3](https://dlmf.nist.gov/28.19.E3): `fₙ=(1/π)∫₀π f(x)meν+2n(-x,q) dx`. The local statements in [Noninteger/Expansions](DLMF/Mathieu/Noninteger/Expansions.lean) use this integral inline. No independently named public `fₙ` map was identified.

### §28.20 Definitions and Basic Properties

<!-- retained entry 214 -->
- **Modified Mathieu equation and rotated angular functions**,
  [28.20.1–7](https://dlmf.nist.gov/28.20.E1): `IsModMathieuSolution`,
  `modMathieuCe`, `modMathieuSe`, `modMathieuMe`, `modMathieuFe`,
  `modMathieuGe` in [Modified/Defs](DLMF/Mathieu/Modified/Basic/Functions.lean#L24).
  Their factors of i and argument rotations follow the separate DLMF
  conventions for Ce, Se, Me, Fe and Ge.

<!-- retained entry 215 -->
- **Parameter h and solutions Mν⁽ʲ⁾, j=1,…,4**,
  [28.20.8–14](https://dlmf.nist.gov/28.20.E8): `modMathieuM`, with
  `ModMathieuAdmissible` and `modMathieuIndex`, in
  [Modified/Defs](DLMF/Mathieu/Modified/Basic/Functions.lean#L123).
  Lean takes h as an argument and uses q=h², rather than selecting h from q.
  Its definition is the Bessel cross-product series of 28.24.1; the large-z
  normalizations in this definition section are characterization theorems.
  Integer-order coefficients inherit the real-q restriction above.

- **Modified-function realizations and normalization**, [28.20.8–20](https://dlmf.nist.gov/28.20.E8): the `DLMF.Mathieu.modMathieuM` object takes `h`, with angular parameter `q=h²`, and is constructed from the Bessel cross-product series of §28.24; the large-argument characterizations are separate statements. The angularly rotated `DLMF.Mathieu.modMathieuCe`, `DLMF.Mathieu.modMathieuSe`, `DLMF.Mathieu.modMathieuMe`, `DLMF.Mathieu.modMathieuFe` and `DLMF.Mathieu.modMathieuGe` provide different named realizations. Integer coefficient selections inherit the real-`q` angular conventions. The `Ie,Io,Ke,Ko` wrappers additionally use `h↦ih` and their prescribed parity-dependent phase and π/2 factors; these factors are part of the definition.

<!-- retained entry 216 -->
- **Radial Mathieu Mcₙ⁽ʲ⁾, Msₙ⁽ʲ⁾ and modified Ieₙ, Ioₙ, Keₙ, Koₙ**,
  [28.20.15–20](https://dlmf.nist.gov/28.20.E15): `radialMathieuMc`,
  `radialMathieuMs`, `modMathieuIe`, `modMathieuIo`, `modMathieuKe`,
  `modMathieuKo` in [Modified/Defs](DLMF/Mathieu/Modified/Basic/Functions.lean#L155).
  These are wrappers with the stated index, h→ih rotation and phase factors.

### §28.22 Connection Formulas

- **Even Mathieu joining factor for Ge**, [DLMF 28.22.E5](https://dlmf.nist.gov/28.22.E5):
  The **joining factor** `g_{e,m}(h)` (DLMF 28.22.5–28.22.6), real `h`:
  `g_{e,2m} = (-1)^m √(2/π) ce_{2m}(π/2, h²) / A^{2m}_0(h²)` and
  `g_{e,2m+1} = (-1)^{m+1} √(2/π) ce'_{2m+1}(π/2, h²) / (h A^{2m+1}_1(h²))`.
  `DLMF.Mathieu.mathieuJoinGe` ([definition](DLMF/Mathieu/Modified/Basic/Functions.lean#L221)).

- **Odd Mathieu joining factor for Go**, [DLMF 28.22.E7](https://dlmf.nist.gov/28.22.E7):
  The **joining factor** `g_{o,m}(h)` (DLMF 28.22.7–28.22.8), real `h`, `m ≥ 1`:
  `g_{o,2m+1} = (-1)^m √(2/π) se_{2m+1}(π/2, h²) / (h B^{2m+1}_1(h²))` and
  `g_{o,2m+2} = (-1)^{m+1} √(2/π) se'_{2m+2}(π/2, h²) / (h² B^{2m+2}_2(h²))`.
  `DLMF.Mathieu.mathieuJoinGo` ([definition](DLMF/Mathieu/Modified/Basic/Functions.lean#L233)).

- **Even Mathieu joining factor for Fe**, [DLMF 28.22.E9](https://dlmf.nist.gov/28.22.E9):
  The **joining factor** `f_{e,m}(h) = -√(π/2) g_{e,m}(h) Mc^{(2)}_m(0, h)` (DLMF 28.22.9).
  `DLMF.Mathieu.mathieuJoinFe` ([definition](DLMF/Mathieu/Modified/Basic/Functions.lean#L245)).

- **Odd Mathieu joining factor for Fo**, [DLMF 28.22.E10](https://dlmf.nist.gov/28.22.E10):
  The **joining factor** `f_{o,m}(h) = -√(π/2) g_{o,m}(h) Ms^{(2)'}_m(0, h)` (DLMF 28.22.10),
  the prime denoting `d/dz`.
  `DLMF.Mathieu.mathieuJoinFo` ([definition](DLMF/Mathieu/Modified/Basic/Functions.lean#L250)).

### §28.23 Expansions in Series of Bessel Functions

- **Analytically continued cylinder-function realizations**, [28.23.1–7](https://dlmf.nist.gov/28.23.E1) and [28.28.17](https://dlmf.nist.gov/28.28.E17): besides the principal-branch `DLMF.Mathieu.mathieuCyl` and logarithmically continued `DLMF.Mathieu.mathieuCylExp`, [Modified/Defs](DLMF/Mathieu/Modified/Basic/Functions.lean#L87) supplies `DLMF.Mathieu.besselJExp`, `DLMF.Mathieu.besselYExp`, `DLMF.Mathieu.mathieuCylCosh`, `DLMF.Mathieu.mathieuCylSinh` and `DLMF.Mathieu.mathieuCylR`. These realize `Jμ(heᶻ)`, `Yμ(heᶻ)`, `𝒞μ⁽ʲ⁾(2h cosh z)`, `𝒞μ⁽ʲ⁾(2h sinh z)` and `𝒞μ⁽ʲ⁾(2hR)` with continuation in `z`. In particular the cosh/sinh forms use `z+log(1±e⁻²ᶻ)` on `Re z>0`; they are not unrestricted substitutions into a principal-branch Bessel function.

  [DLMF 28.23.E1](https://dlmf.nist.gov/28.23.E1):
  The **cylinder functions** `𝒞^{(j)}_μ(h e^z)` of DLMF 28.23.1, continued analytically in
  `z`: `j = 1, 2, 3, 4` give `J_μ`, `Y_μ`, `H^{(1)}_μ = J_μ + i Y_μ`, `H^{(2)}_μ = J_μ - i Y_μ`
  (DLMF 10.4.3); junk `0` for other `j`.
  `DLMF.Mathieu.mathieuCylExp` ([definition](DLMF/Mathieu/Modified/Basic/Functions.lean#L87)).

  [DLMF 28.23.E1](https://dlmf.nist.gov/28.23.E1):
  The principal-branch cylinder functions `𝒞^{(j)}_μ(w)` of DLMF 28.23.1 (`J_μ`, `Y_μ`,
  `H^{(1)}_μ`, `H^{(2)}_μ` at `w`, with `DLMF.Bessel.besselY`); junk `0` for other `j`.
  `DLMF.Mathieu.mathieuCyl` ([definition](DLMF/Mathieu/Modified/Basic/Functions.lean#L99)).

### §28.24 Expansions in Series of Cross-Products of Bessel Functions or
Modified Bessel Functions

- **Cross-product multiplicity εₛ**, [§28.24, 28.24.1–8](https://dlmf.nist.gov/28.24.E1): `DLMF.Mathieu.mathieuEpsilon` in [Modified/Defs](DLMF/Mathieu/Modified/Basic/Functions.lean#L215) is `2` at `s=0` and `1` for positive `s`. This factor belongs to the Bessel cross-product expansions.

### §28.25 Asymptotic Expansions for Large ℜ ⁡ z

- **Large-argument recurrence pair, prefactor and sector**, [28.25.1–5](https://dlmf.nist.gov/28.25.E1): in addition to `DLMF.Mathieu.modMathieuAsympD`, [Modified/Defs](DLMF/Mathieu/Modified/Basic/AsymptoticData.lean#L33) defines `DLMF.Mathieu.modMathieuAsympDPair` for adjacent recurrence coefficients, `DLMF.Mathieu.modMathieuAsympPrefactor` for the oscillatory exponential divided by the continued square root, and `DLMF.Mathieu.modMathieuAsympFilter` for `Re z→+∞` in the prescribed phase strip. The square root is continued as `(2πh)^(1/2) cosh(z/2)`; its branch is part of this realization.

  [DLMF 28.25.E2](https://dlmf.nist.gov/28.25.E2):
  The coefficients `D^±_m` of DLMF 28.25.1, defined by 28.25.2 (`D_{-1} = 0`, `D_0 = 1`) and
  the recurrence 28.25.3; `σ = 1` gives `D^+_m` (for `M^{(3)}_ν`), `σ = -1` gives `D^-_m` (for
  `M^{(4)}_ν`); `a = λ_ν(h²)`.
  `DLMF.Mathieu.modMathieuAsympD` ([definition](DLMF/Mathieu/Modified/Basic/AsymptoticData.lean#L33)).

### §28.26 Asymptotic Approximations for Large q

- **Even Goldstein auxiliary solutions**, [DLMF 28.26.E1](https://dlmf.nist.gov/28.26.E1):
  Goldstein's `Fc_m(z, h)`, defined with `Gc_m` so that 28.26.1 holds:
  `Fc_m = (π h cosh z)^{1/2} (cos φ Mc^{(1)}_m + sin φ Mc^{(2)}_m)`.
  `DLMF.Mathieu.goldsteinFc` ([definition](DLMF/Mathieu/Modified/Basic/AsymptoticData.lean#L59)).

  [DLMF 28.26.E1](https://dlmf.nist.gov/28.26.E1):
  Goldstein's `Gc_m(z, h) = (π h cosh z)^{1/2} (sin φ Mc^{(1)}_m - cos φ Mc^{(2)}_m)`; with
  `Fc_m` it gives `Mc^{(3)}_m = e^{iφ} (π h cosh z)^{-1/2} (Fc_m - i Gc_m)` (DLMF 28.26.1).
  `DLMF.Mathieu.goldsteinGc` ([definition](DLMF/Mathieu/Modified/Basic/AsymptoticData.lean#L67)).

- **Odd Goldstein auxiliary solutions**, [DLMF 28.26.E2](https://dlmf.nist.gov/28.26.E2):
  Goldstein's `Fs_m(z, h) = (π h cosh z)^{1/2} (sin φ Ms^{(1)}_{m+1} - cos φ Ms^{(2)}_{m+1})`;
  with `Gs_m` it gives `i Ms^{(3)}_{m+1} = e^{iφ} (π h cosh z)^{-1/2} (Fs_m - i Gs_m)`
  (DLMF 28.26.2).
  `DLMF.Mathieu.goldsteinFs` ([definition](DLMF/Mathieu/Modified/Basic/AsymptoticData.lean#L75)).

  [DLMF 28.26.E2](https://dlmf.nist.gov/28.26.E2):
  Goldstein's `Gs_m(z, h) = -(π h cosh z)^{1/2} (cos φ Ms^{(1)}_{m+1} + sin φ Ms^{(2)}_{m+1})`
  (DLMF 28.26.2).
  `DLMF.Mathieu.goldsteinGs` ([definition](DLMF/Mathieu/Modified/Basic/AsymptoticData.lean#L84)).

- **Goldstein asymptotic phase**, [DLMF 28.26.E3](https://dlmf.nist.gov/28.26.E3):
  The phase `φ = 2h sinh z - (m + 1/2) arctan(sinh z)` of DLMF 28.26.3 (principal complex
  `arctan`, which is analytic for `Re z > 0`, `|Im z| < π/2`).
  `DLMF.Mathieu.goldsteinPhase` ([definition](DLMF/Mathieu/Modified/Basic/AsymptoticData.lean#L53)).

### §28.28 Integrals, Integral Representations, and Integral Equations

- **Mathieu integral-equation kernel W**, [DLMF 28.28.E1](https://dlmf.nist.gov/28.28.E1):
  `w = cosh z cos t cos α + sinh z sin t sin α` (DLMF 28.28.1).
  `DLMF.Mathieu.mathieuKernelW` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L23)).

- **Improper contour convention ℒ⁽ʲ⁾**, [28.28.6–9](https://dlmf.nist.gov/28.28.E6): `DLMF.Mathieu.mathieuPathIntegral` combines real finite-segment integrals with oriented vertical-ray integrals for `j=1,3,4`, using the factors `±i` from parametrization; other indices give the fallback `0`. The local `DLMF.Mathieu.MathieuPathValley` predicate records the convergence valleys used for those rays. This is additional branch/domain data for the existing kernel integral representations, not a selected numerical quadrature rule.

  [DLMF 28.28.E6](https://dlmf.nist.gov/28.28.E6):
  The integral along the path `𝓛_j` of DLMF 28.28.6, realized as a polygonal path with
  vertical rays: `𝓛_1` from `-η₁ + i∞` down to `-η₁`, along `[-η₁, 2π - η₁]` and up to
  `2π - η₁ + i∞`; `𝓛_3` from `-η₁ + i∞` down to `-η₁`, along `[-η₁, η₂]` and down to
  `η₂ - i∞`; `𝓛_4` from `η₂ - i∞` up to `η₂`, along `[η₂, 2π - η₁]` and up to
  `2π - η₁ + i∞`. Junk `0` for other `j`.
  `DLMF.Mathieu.mathieuPathIntegral` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L28)).

- **Branches of the integral-kernel variables R and φ**, [28.28.17–19](https://dlmf.nist.gov/28.28.E18): `DLMF.Mathieu.mathieuKernelLogR` in [Modified/Defs](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L44) is `(log(1+e⁻²⁽ᶻ⁻ⁱᵗ⁾)+log(1+e⁻²⁽ᶻ⁺ⁱᵗ⁾))/2`; `DLMF.Mathieu.mathieuKernelR` is `exp(z+mathieuKernelLogR)/2`. The companion `DLMF.Mathieu.mathieuKernelPhi` uses the difference of these logarithms. This selects analytic branches on `Re z>0`, with `R(z,0)=cosh z` and `φ(z,0)=0`, rather than using a pointwise principal square root and argument. `DLMF.Mathieu.mathieuCylR` is the corresponding continued cylinder function.

  [DLMF 28.28.E18](https://dlmf.nist.gov/28.28.E18):
  `R(z, t)` of DLMF 28.28.18: the analytic function on `Re z > 0` (real `t`) with
  `R² = ½(cosh 2z + cos 2t)` and `R(z, 0) = cosh z`, written as `R = e^{z + log(2R e^{-z})} / 2`.
  `DLMF.Mathieu.mathieuKernelR` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L50)).

  [DLMF 28.28.E19](https://dlmf.nist.gov/28.28.E19):
  `φ(z, t)` of DLMF 28.28.19: the analytic function on `Re z > 0` (real `t`) with
  `e^{2iφ} = cosh(z + it) / cosh(z - it)` and `φ(z, 0) = 0`:
  `φ = t + (log(1 + e^{-2(z+it)}) - log(1 + e^{-2(z-it)})) / (2i)`.
  `DLMF.Mathieu.mathieuKernelPhi` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L56)).

- **Modified-Mathieu integral-kernel coefficients**, [DLMF 28.28.E24](https://dlmf.nist.gov/28.28.E24):
  `D_0(ν, μ, z) = M^{(3)}_ν(z) M^{(4)}_μ(z) - M^{(4)}_ν(z) M^{(3)}_μ(z)` (DLMF 28.28.24).
  `DLMF.Mathieu.modMathieuD0` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L71)).

  [DLMF 28.28.E24](https://dlmf.nist.gov/28.28.E24):
  `D_1(ν, μ, z) = M^{(3)'}_ν(z) M^{(4)}_μ(z) - M^{(4)'}_ν(z) M^{(3)}_μ(z)` (DLMF 28.28.24).
  `DLMF.Mathieu.modMathieuD1` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L76)).

- **Mathieu kernel integral α₀**, [DLMF 28.28.E27](https://dlmf.nist.gov/28.28.E27):
  `α^{(0)}_{ν,m} = (2π)⁻¹ ∫₀^{2π} cos t me_ν(t, h²) me_{-ν-2m-1}(t, h²) dt`
  (DLMF 28.28.27, first equality).
  `DLMF.Mathieu.mathieuAlpha0` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L82)).

- **Mathieu kernel integral α₁**, [DLMF 28.28.E28](https://dlmf.nist.gov/28.28.E28):
  `α^{(1)}_{ν,m} = (2π)⁻¹ ∫₀^{2π} sin t me_ν(t, h²) me_{-ν-2m-1}(t, h²) dt`
  (DLMF 28.28.28, first equality).
  `DLMF.Mathieu.mathieuAlpha1` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L89)).

- **Integer-order Mathieu kernel integral γ**, [DLMF 28.28.E33](https://dlmf.nist.gov/28.28.E33):
  `γ_{ν,m} = (2π)⁻¹ ∫₀^{2π} me'_ν(t, h²) me_{-ν-2m}(t, h²) dt` (DLMF 28.28.33, first
  equality).
  `DLMF.Mathieu.mathieuGammaInt` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L96)).

- **Radial odd-Mathieu kernel coefficient sequences**, [DLMF 28.28.E35](https://dlmf.nist.gov/28.28.E35):
  `Ds_0(n, m, z) = Ms^{(3)}_n Ms^{(4)}_m - Ms^{(4)}_n Ms^{(3)}_m` (DLMF 28.28.35).
  `DLMF.Mathieu.radialMathieuDs0` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L103)).

  [DLMF 28.28.E35](https://dlmf.nist.gov/28.28.E35):
  `Ds_1(n, m, z) = Ms^{(3)'}_n Ms^{(4)}_m - Ms^{(4)'}_n Ms^{(3)}_m` (DLMF 28.28.35).
  `DLMF.Mathieu.radialMathieuDs1` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L109)).

  [DLMF 28.28.E35](https://dlmf.nist.gov/28.28.E35):
  `Ds_2(n, m, z) = Ms^{(3)'}_n Ms^{(4)'}_m - Ms^{(4)'}_n Ms^{(3)'}_m` (DLMF 28.28.35).
  `DLMF.Mathieu.radialMathieuDs2` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L115)).

- **Odd Mathieu kernel coefficient α-hat**, [DLMF 28.28.E38](https://dlmf.nist.gov/28.28.E38):
  `α̂^{(s)}_{n,m} = (2π)⁻¹ ∫₀^{2π} cos t se_n(t, h²) se_m(t, h²) dt` (DLMF 28.28.38, first
  equality), real `h`.
  `DLMF.Mathieu.mathieuAlphaHatS` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L145)).

- **Radial even-Mathieu kernel coefficient sequences**, [DLMF 28.28.E39](https://dlmf.nist.gov/28.28.E39):
  `Dc_0(n, m, z) = Mc^{(3)}_n Mc^{(4)}_m - Mc^{(4)}_n Mc^{(3)}_m` (DLMF 28.28.39).
  `DLMF.Mathieu.radialMathieuDc0` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L121)).

  [DLMF 28.28.E39](https://dlmf.nist.gov/28.28.E39):
  `Dc_1(n, m, z) = Mc^{(3)'}_n Mc^{(4)}_m - Mc^{(4)'}_n Mc^{(3)}_m` (DLMF 28.28.39).
  `DLMF.Mathieu.radialMathieuDc1` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L127)).

- **Mixed radial-Mathieu kernel coefficient sequences**, [DLMF 28.28.E40](https://dlmf.nist.gov/28.28.E40):
  `Dsc_0(n, m, z) = Ms^{(3)}_n Mc^{(4)}_m - Ms^{(4)}_n Mc^{(3)}_m` (DLMF 28.28.40).
  `DLMF.Mathieu.radialMathieuDsc0` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L133)).

  [DLMF 28.28.E40](https://dlmf.nist.gov/28.28.E40):
  `Dsc_1(n, m, z) = Ms^{(3)'}_n Mc^{(4)}_m - Ms^{(4)'}_n Mc^{(3)}_m` (DLMF 28.28.40).
  `DLMF.Mathieu.radialMathieuDsc1` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L139)).

- **Mathieu kernel coefficient β-hat**, [DLMF 28.28.E43](https://dlmf.nist.gov/28.28.E43):
  `β̂_{n,m} = (2π)⁻¹ ∫₀^{2π} sin t se_n(t, h²) ce_m(t, h²) dt` (DLMF 28.28.43, first
  equality), real `h`.
  `DLMF.Mathieu.mathieuBetaHat` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L152)).

- **Mathieu kernel coefficient γ-hat**, [DLMF 28.28.E46](https://dlmf.nist.gov/28.28.E46):
  `γ̂_{n,m} = (2π)⁻¹ ∫₀^{2π} se'_n(t, h²) ce_m(t, h²) dt` (DLMF 28.28.46, first equality),
  real `h`.
  `DLMF.Mathieu.mathieuGammaHat` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L159)).

- **Even Mathieu kernel coefficient α-hat**, [DLMF 28.28.E49](https://dlmf.nist.gov/28.28.E49):
  `α̂^{(c)}_{n,m} = (2π)⁻¹ ∫₀^{2π} cos t ce_n(t, h²) ce_m(t, h²) dt` (DLMF 28.28.49, first
  equality), real `h`.
  `DLMF.Mathieu.mathieuAlphaHatC` ([definition](DLMF/Mathieu/Modified/Basic/IntegralKernels.lean#L166)).

### §28.29 Definitions and Basic Properties

<!-- retained entry 217 -->
- **Hill equation, periodic potential and normalized fundamental solutions**,
  [28.29.1–6](https://dlmf.nist.gov/28.29.E1): `IsHillSolution`,
  `IsHillPotential`, `hillWI`, `hillWII` in
  [Hill/Defs](DLMF/Mathieu/Hill/Basic.lean#L86). The potential predicate
  requires continuity, period π and mean zero; it does not require π to be
  the least period. Solutions have real independent variable and complex
  values, selected from initial-value solutions; `hill_exists_solution` is
  proved in [Floquet](DLMF/Mathieu/Hill/Floquet.lean#L71).

<!-- retained entry 218 -->
- **Hill Floquet solution, monodromy and discriminant Δ**,
  [28.29.7–15](https://dlmf.nist.gov/28.29.E7):
  `IsHillFloquetSolution`, `hillMonodromy`, `hillDiscriminant` in
  [Hill/Defs](DLMF/Mathieu/Hill/Basic.lean#L121).

- **Hill discriminant and periodic Floquet factor**, [28.29.7–15](https://dlmf.nist.gov/28.29.E7): `DLMF.Mathieu.hillDiscriminant` is the full monodromy trace `Δ`, not the half-trace. `DLMF.Mathieu.IsHillFloquetSolution` records the multiplier relation; the periodic factor `Pν(x)=e⁻ⁱνˣFν(x)` is not a separate chosen function. The predicate `DLMF.Mathieu.IsHillPotential` requires a continuous complex-valued π-periodic zero-mean potential, without requiring π to be its least positive period.

<!-- retained entry 219 -->
- **Periodic and antiperiodic eigenvalues λₙ, μₙ and merged sequence λ̂ₙ**,
  [28.29.16–18](https://dlmf.nist.gov/28.29.E16):
  `hillPeriodicEigenvalue`, `hillAntiperiodicEigenvalue`, `hillEigenvalueHat`,
  with `hillMultiplierSolutions` and `hillEigenCount`, in
  [Hill/Defs](DLMF/Mathieu/Hill/Basic.lean#L168). Their infimum construction
  counts eigenspace dimensions, hence retains DLMF's repeated eigenvalues;
  μ₀ is a fallback outside DLMF's indexing.

<!-- retained entry 220 -->
- **Mean square N**, [28.29.19](https://dlmf.nist.gov/28.29.E19):
  `hillMeanSquare` in [Hill/Defs](DLMF/Mathieu/Hill/Basic.lean#L225).

### §28.30 Expansions in Series of Eigenfunctions

- **Normalized Hill eigenfunction family and expansion coefficients**, [§28.30(i), 28.30.1–3](https://dlmf.nist.gov/28.30.i): `DLMF.Mathieu.IsHillEigenfunctionFamily` is a predicate on a proposed family `wₘ`, including the normalization `(1/(2π))∫₀²π wₘwₙ=δₘₙ`. It does not choose a canonical family inside repeated eigenspaces. The coefficient `(1/(2π))∫₀²π f(x)wₘ(x) dx` occurs inline in the expansion statements; there is no separate selected coefficient map.

  [DLMF 28.30.i](https://dlmf.nist.gov/28.30.i):
  `w : ℕ → ℝ → ℝ` is an **orthonormal set of eigenfunctions** of Hill's equation with real
  potential `Q` (DLMF 28.30.1–28.30.2): each `w m` is a `2π`-periodic solution with
  `λ = λ̂_m`, and `(2π)⁻¹ ∫₀^{2π} w_m w_n = δ_{mn}`.
  `DLMF.Mathieu.IsHillEigenfunctionFamily` ([definition](DLMF/Mathieu/Hill/Basic.lean#L215)).

### §28.31 Equations of Whittaker–Hill and Ince

- **Whittaker–Hill equation predicate**, [DLMF 28.31.E1](https://dlmf.nist.gov/28.31.E1):
  The **equation of Whittaker–Hill** (DLMF 28.31.1),
  `W'' + (A + B cos 2z - ½ (kc)² cos 4z) W = 0`, for an entire function `W` and constants
  `A, B, k, c`.
  `DLMF.Mathieu.IsWhittakerHillSolution` ([definition](DLMF/Mathieu/Hill/Basic.lean#L232)).

- **Ince polynomial spaces and eigenvalues aₚᵐ, bₚᵐ**, [§28.31(ii), 28.31.10–12](https://dlmf.nist.gov/28.31.ii): [Hill/Defs](DLMF/Mathieu/Hill/Basic.lean#L252) defines `DLMF.Mathieu.inceFrequencies` as the frequencies `k≤p` with `k≡p (mod 2)`, `DLMF.Mathieu.IsInceCosPoly` and `DLMF.Mathieu.IsInceSinPoly` as the corresponding real-coefficient trigonometric polynomial spaces, and `DLMF.Mathieu.zerosIco` as the number of zeros on `[0,π)`. The eigenvalue choices `DLMF.Mathieu.inceA` and `DLMF.Mathieu.inceB` select the unique real parameter admitting a nonzero polynomial solution with `m` zeros, and otherwise give `0`; the sine zero at `0` is counted. The already listed `DLMF.Mathieu.inceC` and `DLMF.Mathieu.inceS` then normalize the square integral and choose the positive value, respectively positive derivative, at zero. Invalid index choices do not describe new Ince eigenfunctions. The intended valid-index characterization still relies on the admitted `DLMF.Mathieu.inceC_spec` and `DLMF.Mathieu.inceS_spec` ([Ince](DLMF/Mathieu/Hill/Basic.lean#L269)); the conditional choices alone do not prove existence.

  [DLMF 28.31.E10](https://dlmf.nist.gov/28.31.E10):
  The **Ince polynomial** `C_p^m(z, ξ)` (DLMF 28.31.10) for real `ξ`: the cosine Ince
  polynomial solution of 28.31.3 with `η = a_p^m(ξ)`, normalized by
  `(1/π) ∫₀^{2π} (C_p^m)² dx = 1` (28.31.12) and `C_p^m(0, ξ) > 0`. Definition by choice; `0`
  if it does not exist uniquely.
  `DLMF.Mathieu.inceC` ([definition](DLMF/Mathieu/Hill/Basic.lean#L283)).

  [DLMF 28.31.E11](https://dlmf.nist.gov/28.31.E11):
  The **Ince polynomial** `S_p^m(z, ξ)` (DLMF 28.31.11) for real `ξ`: the sine Ince
  polynomial solution of 28.31.3 with `η = b_p^m(ξ)`, normalized by 28.31.12 and with
  `S_p^m'(0, ξ) > 0`. Definition by choice; `0` if it does not exist uniquely.
  `DLMF.Mathieu.inceS` ([definition](DLMF/Mathieu/Hill/Basic.lean#L293)).

- **Ince equation predicate**, [DLMF 28.31.E3](https://dlmf.nist.gov/28.31.E3):
  The **equation of Ince** (DLMF 28.31.3),
  `w'' + ξ sin(2z) w' + (η - p ξ cos(2z)) w = 0`, for an entire function `w`.
  `DLMF.Mathieu.IsInceSolution` ([definition](DLMF/Mathieu/Hill/Basic.lean#L240)).

- **Even paraboloidal wave function hc**, [DLMF 28.31.E16](https://dlmf.nist.gov/28.31.E16):
  The **paraboloidal wave function** `hc_p^m(z, ξ) = e^{-ξ cos(2z)/4} C_p^m(z, ξ)`
  (DLMF 28.31.16).
  `DLMF.Mathieu.paraboloidalHc` ([definition](DLMF/Mathieu/Hill/Basic.lean#L302)).

- **Odd paraboloidal wave function hs**, [DLMF 28.31.E17](https://dlmf.nist.gov/28.31.E17):
  The **paraboloidal wave function** `hs_p^m(z, ξ) = e^{-ξ cos(2z)/4} S_p^m(z, ξ)`
  (DLMF 28.31.17).
  `DLMF.Mathieu.paraboloidalHs` ([definition](DLMF/Mathieu/Hill/Basic.lean#L308)).

### §28.32 Mathematical Applications

- **Elliptical and paraboloidal coordinate maps**, [28.32.1 and 28.32.7](https://dlmf.nist.gov/28.32.E1): elliptical coordinates are `x=c cosh ξ cos η`, `y=c sinh ξ sin η`; §28.32(ii) gives the three displayed paraboloidal coordinates. The section also defines the transformed solution `w(z)=∫ℒ K(z,ζ)u(ζ)dζ` under the kernel equation and endpoint condition. No dedicated local public coordinate-map or general kernel-transform object was identified. These are recorded as definitions occurring in mathematical application notes; those application notes remain outside new theorem acquisition.

### §28.33 Physical Applications

- **Membrane eigenparameters and the stability ray**, [28.33.3–4](https://dlmf.nist.gov/28.33.E3): `qₙ,ₘ` denotes the positive roots of the radial boundary determinant, with `ωₙ,ₘ²=4qₙ,ₘτ/(c²ρ)`. In the pendulum scaling, `a=b/ω²`, `2q=f/ω²`, and the first-quadrant ray is `a=(2b/f)q`. No separate local selected root, frequency, or ray object was identified. These are definitions in physical application notes, outside new theorem acquisition; the abstract stability predicate is already `DLMF.Mathieu.IsMathieuStable`.

### §28.35 Tables

- **Exact renormalizations used in tables**, [§28.35(i)](https://dlmf.nist.gov/28.35.i): Blanch–Rhodes use `t=√q/2`, `Beₙ(t)=aₙ(q)+2q-(4n+2)√q` and `Boₙ(t)=bₙ(q)+2q-(4n-2)√q`; Ince's labels satisfy `beₙ=aₙ+2q`, `boₙ=bₙ+2q`; Stratton's labels are `bₙ=aₙ+2q`, `bₙ′=bₙ(q)+2q`, with `c=2√q`. Here Stratton's prime distinguishes labels and is not a derivative. These exact aliases can be expressed using the existing characteristic values, but have no separate public wrappers. Tabulated decimal values, precision claims and numerical zero lists are excluded: numerical.

## Chapter 29 — Lamé functions

Expanded review: all 22 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§29.1–29.22 checked; matching headings are §§29.3 and 29.12.
Names below are in `DLMF.Lame`; the prefix `Real` is nested in that namespace.

### §29.1 Special Notation

- **Modulus, complementary modulus, alternative Lamé notation and normalization**, [DLMF §29.1](https://dlmf.nist.gov/29.1):
  DLMF assumes real h,ν, 0<k<1 and ν≥−1/2, with k′=√(1−k²), K=K(k), K′=K(k′).
  The Lean Lamé interfaces take the modulus k, although the DLMF family names
  display k². Jansen's Lc/Ls use ψ=am(z,k), complementary parameter k′² and
  parity-dependent factors (−1)^m; Ince interchanges the odd a and b eigenvalue
  names. The positive Ince conversion factors cν^m,sν^m satisfy
  c²=(4/π)∫₀ᴷEc² dx and s²=(4/π)∫₀ᴷEs² dx, without a dn weight. No separately
  named Lean constructions of these alternative functions or conversion factors
  were found. They must be distinguished from the dn-weighted DLMF normalization
  in `DLMF.Lame.Real.IsNormalizedLameEigenfunction`
  ([source](DLMF/Lame/Basic/SpectralData.lean#L64)).

### §29.2 Differential Equations

- **Jacobi-form Lamé solution predicate**, [DLMF 29.2.E1](https://dlmf.nist.gov/29.2.E1):
  Lamé's equation (DLMF 29.2.1) over `ℂ` on a set `U`:
  `w'' + (h - ν(ν+1) k² sn²(z, k)) w = 0`, with `w` and `w'` complex differentiable at every
  point of `U`. DLMF takes `0 < k < 1`, `ν ≥ -1/2` and `h` real; the predicate is stated for all
  complex parameters.
  `DLMF.Lame.IsLameSolutionOn` ([definition](DLMF/Lame/Basic/Equations.lean#L26)).

- **Algebraic Lamé solution predicate**, [DLMF 29.2.E2](https://dlmf.nist.gov/29.2.E2):
  The algebraic form of Lamé's equation (DLMF 29.2.2) in `ξ = sn²(z, k)` (29.2.3):
  `w'' + ½(1/ξ + 1/(ξ-1) + 1/(ξ-k⁻²)) w' + (h k⁻² - ν(ν+1)ξ)/(4ξ(ξ-1)(ξ-k⁻²)) w = 0` on `U`.
  `DLMF.Lame.IsLameAlgebraicSolutionOn` ([definition](DLMF/Lame/Basic/Equations.lean#L38)).

- **Algebraic, trigonometric and Weierstrass variables**, [DLMF 29.2.E3](https://dlmf.nist.gov/29.2.E3), [29.2.E5–12](https://dlmf.nist.gov/29.2.E5):
  ξ=sn²(z,k) is a composed expression; φ=π/2−am(z,k) is
  `DLMF.Lame.Real.lamePhi` ([source](DLMF/Lame/Basic/Equations.lean#L106)).
  The real constants e₁>e₂>e₃ satisfy e₁+e₂+e₃=0 and
  (e₂−e₃)/(e₁−e₃)=k² and are not uniquely chosen by k.
  g=(e₁−e₃)h+ν(ν+1)e₃, η=(e₁−e₃)⁻¹ᐟ²(z−iK′),
  ζ=℘(η;g₂,g₃), g₂=−4(e₂e₃+e₃e₁+e₁e₂), g₃=4e₁e₂e₃ are explicit
  parameters and expressions in the equation-change theorems
  ([source](DLMF/Lame/DifferentialEquations.lean#L296)).
  `DLMF.Lame.IsLameSolutionOn`, `DLMF.Lame.IsLameAlgebraicSolutionOn`,
  `DLMF.Lame.Real.IsLameTrigSolution`, `DLMF.Lame.IsLameWeierstrassSolutionOn`
  and `DLMF.Lame.IsLameWeierstrassAlgebraicSolutionOn` encode the five equations
  ([source](DLMF/Lame/Basic/Equations.lean#L26)). These predicates allow more general
  parameters; singular points must still be excluded when interpreting the
  differential equations.

  [DLMF 29.2.E4](https://dlmf.nist.gov/29.2.E4):
  The trigonometric form of Lamé's equation (DLMF 29.2.4) for real `φ`:
  `(1 - k² cos²φ) w'' + k² cos φ sin φ w' + (h - ν(ν+1) k² cos²φ) w = 0`.
  `DLMF.Lame.Real.IsLameTrigSolution` ([definition](DLMF/Lame/Basic/Equations.lean#L93)).

  [DLMF 29.2.E5](https://dlmf.nist.gov/29.2.E5):
  The variable `φ = π/2 - am(x, k)` of DLMF 29.2.5 for real `x` (`am` is the real amplitude
  `Real.jacobiAmm x (k²)` of §22.16(i)); then `cos φ = sn(x, k)` and `sin φ = cn(x, k)`.
  `DLMF.Lame.Real.lamePhi` ([definition](DLMF/Lame/Basic/Equations.lean#L106)).

  [DLMF 29.2.E9](https://dlmf.nist.gov/29.2.E9):
  The Weierstrass form of Lamé's equation (DLMF 29.2.9) in `η`:
  `w'' + (g - ν(ν+1) ℘(η; g₂, g₃)) w = 0` on `U`, with the project's `℘(η; g₂, g₃)`
  (`DLMF.Weierstrass.weierstrassPInvariants`).
  `DLMF.Lame.IsLameWeierstrassSolutionOn` ([definition](DLMF/Lame/Basic/Equations.lean#L49)).

  [DLMF 29.2.E10](https://dlmf.nist.gov/29.2.E10):
  The algebraic Weierstrass form of Lamé's equation (DLMF 29.2.10) in `ζ = ℘(η)`:
  `w'' + ½ ∑ⱼ 1/(ζ - eⱼ) w' + (g - ν(ν+1)ζ)/(4 ∏ⱼ (ζ - eⱼ)) w = 0` on `U`.
  `DLMF.Lame.IsLameWeierstrassAlgebraicSolutionOn` ([definition](DLMF/Lame/Basic/Equations.lean#L60)).

### §29.3 Definitions and Basic Properties

<!-- retained entry 221 -->
- **Four Lamé spectra aν²ᵐ, aν²ᵐ⁺¹, bν²ᵐ⁺¹, bν²ᵐ⁺²**,
  [§29.3(i) and Table 29.3.1](https://dlmf.nist.gov/29.3.i):
  `Real.lameSpectrum`, `Real.IsNthLameEigenvalue`, `Real.lameEigenvalue`,
  `Real.lameAk`, `Real.lameBk`, with `Real.LameBoundary`,
  `Real.IsLameSolution`, `Real.IsLameEigenfunction`, in
  [Basic](DLMF/Lame/Basic/Equations.lean#L82). Boolean boundary types distinguish
  vanishing values and derivatives. Lean takes the modulus k, even where
  DLMF writes k². The chosen ordered eigenvalues have a proved
  characterization `Real.lameEigenvalue_spec` for ν≥−1/2 and 0<k<1 in
  [Eigenvalues](DLMF/Lame/Eigenvalues.lean#L95).

- **Four ordered spectra, endpoint conditions and normalized real functions**, [DLMF §29.3(i)](https://dlmf.nist.gov/29.3.i), [Table 29.3.2](https://dlmf.nist.gov/29.3.T2), [29.3.E18](https://dlmf.nist.gov/29.3.E18):
  `DLMF.Lame.Real.LameBoundary`, `DLMF.Lame.Real.IsLameEigenfunction`,
  `DLMF.Lame.Real.lameSpectrum`, `DLMF.Lame.Real.IsNthLameEigenvalue`,
  `DLMF.Lame.Real.lameEigenvalue`, `DLMF.Lame.Real.lameAk` and
  `DLMF.Lame.Real.lameBk` ([source](DLMF/Lame/Basic/SpectralData.lean#L23)) distinguish
  the four separated problems on [0,K]. In order a^(2m),a^(2m+1),b^(2m+1),b^(2m+2),
  the boundary types are Neumann–Neumann, Dirichlet–Neumann,
  Neumann–Dirichlet, Dirichlet–Dirichlet. The selected spectrum index is m;
  the displayed superscript counts zeros on [0,2K). The normalized functions
  `DLMF.Lame.Real.lameEigenfunction`, `DLMF.Lame.Real.lameEck` and
  `DLMF.Lame.Real.lameEsk` use ∫₀ᴷdn(x,k)w(x)²dx=π/4, Ec(K)>0 or Es′(K)<0.
  These are real-variable constructions, with zero fallbacks if their defining
  characterizations have no unique solution; complex-argument continuation is a
  separate gap.

<!-- retained entry 223 -->
- **H, recurrence coefficients and continued-fraction quantities**,
  [29.3.9–17](https://dlmf.nist.gov/29.3.E9): the shifted eigenvalue H is
  the displayed arithmetic expression; the four recurrence families are
  encoded by `LameRecurrence`, `LameRecurrence.alpha`, `LameRecurrence.beta`,
  `LameRecurrence.gamma`, `LameRecurrence.Satisfies`, `lameCFLeft`, `lameCFRight` in
  [Basic](DLMF/Lame/Basic/RecurrenceData.lean#L23). These are coefficient and recurrence
  objects, rather than independent definitions of Ec or Es.

- **Shifted eigenvalue, eight coefficient triples and finite continued fractions**, [DLMF 29.3.E9–17](https://dlmf.nist.gov/29.3.E9), [29.6.E11](https://dlmf.nist.gov/29.6.E11), [29.6.E26](https://dlmf.nist.gov/29.6.E26), [29.6.E41](https://dlmf.nist.gov/29.6.E41), [29.6.E56](https://dlmf.nist.gov/29.6.E56):
  H=2a−ν(ν+1)k², or the corresponding expression with b, is an arithmetic
  expression. `DLMF.Lame.LameRecurrence` selects A0,A1,B1,B2,C0,C1,D1,D2;
  `DLMF.Lame.LameRecurrence.alpha`, `DLMF.Lame.LameRecurrence.beta` and
  `DLMF.Lame.LameRecurrence.gamma` give α_p,β_p,γ_p, including their exceptional
  p=0 formulas ([source](DLMF/Lame/Basic/RecurrenceData.lean#L23)).
  `DLMF.Lame.LameRecurrence.Satisfies` encodes the coefficient recurrence.
  `DLMF.Lame.lameCFLeft` and `DLMF.Lame.lameCFRight` are finite rational
  recursions, with the latter taking an explicit truncation depth
  ([source](DLMF/Lame/Basic/RecurrenceData.lean#L93)). Their totalized divisions do not make
  a denominator zero into a valid classical continued-fraction value; infinite
  convergence and terminating polynomial cases are additional statements.

<!-- retained entry 222 -->
- **Normalized Lamé functions Ecν, Esν**,
  [Table 29.3.2 and 29.3.18](https://dlmf.nist.gov/29.3.T2):
  `Real.IsNormalizedLameEigenfunction`, `Real.lameEigenfunction`,
  `Real.lameEck`, `Real.lameEsk` in [Basic](DLMF/Lame/Basic/SpectralData.lean#L64).
  These use the weighted dn integral and endpoint sign rules.
  `Real.lameEigenfunction_spec` proves existence and uniqueness on the same
  real parameter domain in [Eigenvalues](DLMF/Lame/Eigenvalues.lean#L158).

### §29.5 Special Cases and Limiting Forms

- **Zero-modulus trigonometric forms and limiting parameters**, [DLMF 29.5.E2–7](https://dlmf.nist.gov/29.5.E2):
  The k=0 formulas Ec₀=1/√2 and the positive-index cosine/sine formulas are
  identities for the preceding functions. `DLMF.Lame.p2p_phi`
  ([source](DLMF/Lame/SpecialCases.lean#L160)) is the explicit trigonometric
  representative used to identify them. μ=max(ν−m,0) in the k→1 limit and
  k²ν(ν+1)=4θ in the Mathieu limit are expressions and scaling conditions;
  they do not define additional normalized special functions.

### §29.6 Fourier Series

- **Direct and dn-factored Fourier coefficient families**, [DLMF 29.6.E1](https://dlmf.nist.gov/29.6.E1), [29.6.E8](https://dlmf.nist.gov/29.6.E8), [29.6.E16](https://dlmf.nist.gov/29.6.E16), [29.6.E23](https://dlmf.nist.gov/29.6.E23), [29.6.E31](https://dlmf.nist.gov/29.6.E31), [29.6.E38](https://dlmf.nist.gov/29.6.E38), [29.6.E46](https://dlmf.nist.gov/29.6.E46), [29.6.E53](https://dlmf.nist.gov/29.6.E53):
  `DLMF.Lame.Real.lameCosCoeff` and `DLMF.Lame.Real.lameSinCoeff`
  ([source](DLMF/Lame/Basic/RecurrenceData.lean#L110)) define the A/B families with a dn weight
  and the C/D families with unit weight, all in φ=π/2−am(x,k). The latter are
  coefficients of w/dn, so w is reconstructed with an exterior dn factor.
  The even cosine constant is ½A₀ or ½C₀. Parity selects the even/odd frequency
  lists; the eight recurrence choices above retain these different conventions.

### §29.7 Asymptotic Expansions

- **Large-order scale and displayed exact coefficients**, [DLMF 29.7.E2–8](https://dlmf.nist.gov/29.7.E2):
  `DLMF.Lame.lameKappa` is κ=k√(ν(ν+1)), with p=2m+1 an expression.
  `DLMF.Lame.lameTau0`, `DLMF.Lame.lameTau1`, `DLMF.Lame.lameTau2`,
  `DLMF.Lame.lameTau3` and `DLMF.Lame.lameTau4`
  ([source](DLMF/Lame/Basic/RecurrenceData.lean#L134)) are the five displayed exact coefficient
  polynomials. They are distinct finite-index definitions; no named all-order
  τ_j sequence was found. Exact asymptotic coefficients remain in scope.

  [DLMF 29.7.E2](https://dlmf.nist.gov/29.7.E2):
  `κ = k(ν(ν+1))^{1/2}` (DLMF 29.7.2).
  `DLMF.Lame.lameKappa` ([definition](DLMF/Lame/Basic/RecurrenceData.lean#L134)).

  [DLMF 29.7.E3](https://dlmf.nist.gov/29.7.E3):
  The coefficient `τ₀ = (1 + k²)(1 + p²)/2³` (DLMF 29.7.3).
  `DLMF.Lame.lameTau0` ([definition](DLMF/Lame/Basic/RecurrenceData.lean#L138)).

  [DLMF 29.7.E4](https://dlmf.nist.gov/29.7.E4):
  The coefficient `τ₁ = p((1 + k²)²(p² + 3) - 4k²(p² + 5))/2⁶` (DLMF 29.7.4).
  `DLMF.Lame.lameTau1` ([definition](DLMF/Lame/Basic/RecurrenceData.lean#L142)).

  [DLMF 29.7.E6](https://dlmf.nist.gov/29.7.E6):
  The coefficient `τ₂ = (1 + k²)(1 - k²)²(5p⁴ + 34p² + 9)/2¹⁰` (DLMF 29.7.6).
  `DLMF.Lame.lameTau2` ([definition](DLMF/Lame/Basic/RecurrenceData.lean#L146)).

  [DLMF 29.7.E7](https://dlmf.nist.gov/29.7.E7):
  The coefficient `τ₃` of DLMF 29.7.7.
  `DLMF.Lame.lameTau3` ([definition](DLMF/Lame/Basic/RecurrenceData.lean#L150)).

  [DLMF 29.7.E8](https://dlmf.nist.gov/29.7.E8):
  The coefficient `τ₄` of DLMF 29.7.8.
  `DLMF.Lame.lameTau4` ([definition](DLMF/Lame/Basic/RecurrenceData.lean#L157)).

### §29.8 Integral Equations

- **Kernel arguments and period-shift constant**, [DLMF 29.8.E1–6](https://dlmf.nist.gov/29.8.E1):
  x=k²∏sn−(k²/k′²)∏cn+(1/k′²)∏dn, where each product has the four arguments
  z,z₁,z₂,z₃; y=dn(z,k)dn(z₁,k)/k′. The constants σ=±1 and τ are the period-shift
  data of w,w₂, and μ=2στ/W{w,w₂}. These are explicit expressions and
  hypotheses in `DLMF.Lame.Real.lame_integral_equation` and its special cases
  ([source](DLMF/Lame/IntegralEquations.lean#L40)); no separate kernel-argument
  definitions were found. DLMF prints a Ferrers P kernel, but the real arguments
  need not lie in (−1,1). The Lean statements use
  `DLMF.Legendre.legendreP` as the hypergeometric continuation; this agrees with
  Ferrers P on its real interval but has a larger principal-branch domain.

### §29.9 Stability

- **Stability of the differential equation**, [DLMF §29.9](https://dlmf.nist.gov/29.9):
  `DLMF.Lame.Real.IsLameStable` ([source](DLMF/Lame/Basic/RecurrenceData.lean#L126)) means
  that every real solution is bounded on ℝ. Existence of one bounded periodic
  solution alone is insufficient for this definition.

  [DLMF 29.9](https://dlmf.nist.gov/29.9):
  Lamé's equation 29.2.1 with parameters `k, h, ν` is stable if all its real solutions are
  bounded on `ℝ` (DLMF §29.9).
  `DLMF.Lame.Real.IsLameStable` ([definition](DLMF/Lame/Basic/RecurrenceData.lean#L126)).

### §29.10 Lamé Functions with Imaginary Periods

- **Complementary-modulus transformation and imaginary-period functions**, [DLMF 29.10.E1–4](https://dlmf.nist.gov/29.10.E1):
  h′=ν(ν+1)−h and z′=i(z−K−iK′) are expressions in the change-of-equation
  theorem `DLMF.Lame.isLameSolutionOn_imaginary`
  ([source](DLMF/Lame/DifferentialEquations.lean#L527)). DLMF's Ec/Es(z′,k′²)
  require complex continuation of these functions. The current real-variable
  constructions give the restriction z=K+is, z′=K′−s; the corresponding
  solution/period statements are `DLMF.Lame.Real.lameEck_imaginary_solution`,
  `DLMF.Lame.Real.lameEsk_imaginary_solution` and
  `DLMF.Lame.Real.lame_imaginary_periods`
  ([source](DLMF/Lame/DifferentialEquations.lean#L658)). They do not construct
  the full normalized complex Ec/Es family.

### §29.11 Lamé Wave Equation

- **Lamé-wave solution predicate**, [DLMF 29.11.E1](https://dlmf.nist.gov/29.11.E1):
  The Lamé (ellipsoidal) wave equation (DLMF 29.11.1) on `U`:
  `w'' + (h - ν(ν+1) k² sn²(z, k) + k² ω² sn⁴(z, k)) w = 0`.
  `DLMF.Lame.IsLameWaveSolutionOn` ([definition](DLMF/Lame/Basic/Equations.lean#L72)).

### §29.12 Definitions

<!-- retained entry 224 -->
- **Eight families of Lamé polynomials**,
  [29.12.1–8 and Table 29.12.1](https://dlmf.nist.gov/29.12.E1):
  `LamePolyType`, `lamePolyEk`, and its wrappers `lameUEk`, `lameSEk`,
  `lameCEk`, `lameDEk`, `lameSCEk`, `lameSDEk`, `lameCDEk`, `lameSCDEk`
  in [Polynomials/Defs](DLMF/Lame/Polynomials/Basic.lean#L52).
  These are finite Chebyshev expansions with sn/cn/dn prefactors, not
  choices from the preceding eigenfunction family. `lamePolyH` and
  `lamePolyCoeff` use the finite matrix `lameMatrix`, its sorted
  characteristic-polynomial roots `lameMatrixEigenvalue`, and recurrence
  eigenvectors `lameRecVec`; `LamePolyType.order`, `LamePolyType.signForm`,
  `LamePolyType.normForm`, `LamePolyType.prefactor`, `LamePolyType.basis`
  encode the order, sign, normalization and basis conventions.

- **Eight polynomial types and correlated algebraic branches**, [DLMF Table 29.12.1](https://dlmf.nist.gov/29.12.T1), [29.12.E9–10](https://dlmf.nist.gov/29.12.E9):
  `DLMF.Lame.LamePolyType` and `DLMF.Lame.LamePolyType.order` distinguish
  uE,sE,cE,dE,scE,sdE,cdE,scdE and their orders 2n,2n+1,2n+2,2n+3
  ([source](DLMF/Lame/Polynomials/Basic.lean#L52)). The functions are
  polynomials in sn,cn,dn and doubly periodic meromorphic functions of z.
  Their algebraic form ξ^ρ(ξ−1)^σ(ξ−k⁻²)^τP(ξ), ρ,σ,τ∈{0,½}, carries branches
  inherited from sn,cn,dn; arbitrary independent principal powers do not give
  the same global function. `DLMF.Lame.lamePolyEk_algebraic_form`
  ([source](DLMF/Lame/Polynomials/Series.lean#L625)) expresses the polynomial
  factor with these Jacobi prefactors. The polynomial and its ordered zero
  tuple are existential data, rather than a second chosen function or root list.

<!-- retained entry 225 -->
- **Algebraic polynomial form and ordered zeros ξ₁,…,ξₙ**,
  [29.12.9–10](https://dlmf.nist.gov/29.12.E9): the algebraic form is a
  bridge theorem `lamePolyEk_algebraic_form` in
  [Polynomials/Series](DLMF/Lame/Polynomials/Series.lean#L625), not a second
  selected Lamé polynomial. The zeros are quantified tuples in that theorem
  family, rather than a defined root-list object.

<!-- retained entry 226 -->
- **Zero-maximization function g and region R**,
  [29.12.11–12](https://dlmf.nist.gov/29.12.E11): explicit local expressions
  in `lamePolyEk_zeros_maximize` in
  [Polynomials/Series](DLMF/Lame/Polynomials/Series.lean#L643), with no
  separately named global definitions.

- **Electrostatic zero density and ordered chamber**, [DLMF 29.12.E11–13](https://dlmf.nist.gov/29.12.E11):
  g(t)=∏ₚtₚ^(ρ+¼)|tₚ−1|^(σ+¼)(k⁻²−tₚ)^(τ+¼)∏_{q<r}(tᵣ−t_q), on
  R={0≤t₁≤⋯≤t_m≤1≤t_(m+1)≤⋯≤t_n≤k⁻²}. These are explicit local expressions
  in `DLMF.Lame.lamePolyEk_zeros_maximize`
  ([source](DLMF/Lame/Polynomials/Series.lean#L643)), with no independent
  global definitions. The equilibrium equations characterize the zero tuple
  through reciprocal-distance sums; they introduce no additional function.

### §29.14 Orthogonality

- **Two-variable polynomial products, weight and bilinear integral**, [DLMF 29.14.E1–11](https://dlmf.nist.gov/29.14.E1):
  `DLMF.Lame.lameProduct` forms E(s)E(K+it) for each of the eight types;
  `DLMF.Lame.lameOrthWeight` is sn²(K+it,k)−sn²(s,k);
  `DLMF.Lame.lameInner` is the iterated integral of weight·g·h, with no complex
  conjugation ([source](DLMF/Lame/Polynomials/Basic.lean#L218)). The first
  rectangle is [0,K]×[0,K′]; the combined eight-type orthogonality uses
  [0,4K]×[0,2K′]. These domain conventions differ and are explicit arguments.

  [DLMF 29.14.E1](https://dlmf.nist.gov/29.14.E1):
  The product `E(s, k²) E(K + it, k²)` of a Lamé polynomial of type `t` at `s` and at
  `K + it` (DLMF 29.14.1, 29.14.4–29.14.10).
  `DLMF.Lame.lameProduct` ([definition](DLMF/Lame/Polynomials/Basic.lean#L230)).

  [DLMF 29.14.E2](https://dlmf.nist.gov/29.14.E2):
  The inner product `⟨g, h⟩ = ∫₀^a ∫₀^b w(s, t) g(s, t) h(s, t) dt ds` of DLMF 29.14.2
  (`a = K`, `b = K'`) and 29.14.11 (`a = 4K`, `b = 2K'`); no complex conjugation, as in DLMF.
  `DLMF.Lame.lameInner` ([definition](DLMF/Lame/Polynomials/Basic.lean#L224)).

  [DLMF 29.14.E3](https://dlmf.nist.gov/29.14.E3):
  The weight `w(s, t) = sn²(K + it, k) - sn²(s, k)` of DLMF 29.14.3 (real `s, t`; it is real
  and nonnegative on `[0, K] × [0, K']`).
  `DLMF.Lame.lameOrthWeight` ([definition](DLMF/Lame/Polynomials/Basic.lean#L218)).

### §29.15 Fourier Series and Chebyshev Series

- **Finite matrix, sorted eigenvalues and recurrence eigenvectors**, [DLMF 29.15.E2–4](https://dlmf.nist.gov/29.15.E2):
  `DLMF.Lame.lameMatrix` has β on its diagonal, α above and γ below;
  `DLMF.Lame.lameMatrixEigenvalue` sorts its real characteristic-polynomial
  roots, and `DLMF.Lame.lameRecVecPair`, `DLMF.Lame.lameRecVec` generate the
  forward recurrence from v₋₁=0,v₀=1
  ([source](DLMF/Lame/Polynomials/Basic.lean#L127)).
  `DLMF.Lame.LamePolyType.recurrence` selects the appropriate one of the eight
  recurrence systems; `DLMF.Lame.lamePolyH` is its mth H value. The domain
  0<k<1, 0≤m≤n is needed for the intended real simple spectrum and for the
  nonzero recurrence denominators. Sorting roots with a zero fallback alone
  does not establish these spectral properties.

- **Polynomial coefficient normalization and sign forms**, [DLMF 29.15.E5–6](https://dlmf.nist.gov/29.15.E5), [29.15.E10–41](https://dlmf.nist.gov/29.15.E10):
  `DLMF.Lame.LamePolyType.normForm` and `DLMF.Lame.LamePolyType.signForm`
  ([source](DLMF/Lame/Polynomials/Basic.lean#L73)) are the eight quadratic
  normalization and linear sign forms. The conditions are normForm=1 and
  signForm>0. The dE,sdE,cdE,scdE quadratic forms contain the prescribed
  k-dependent neighboring-coefficient terms, rather than a universal Euclidean
  norm. `DLMF.Lame.lamePolyCoeff` uses both forms to normalize the recurrence
  vector and sets coefficients beyond n to zero. The conversion
  h=(H_m+ν(ν+1)k²)/2 is a theorem expression.

- **Independent finite Chebyshev construction of the eight functions**, [DLMF 29.15.E43–50](https://dlmf.nist.gov/29.15.E43):
  `DLMF.Lame.LamePolyType.prefactor` and `DLMF.Lame.LamePolyType.basis` supply
  the cn/dn factors and even/odd Chebyshev T/U bases, including the half constant
  term. `DLMF.Lame.lamePolyEk` is the resulting finite sum, with wrappers
  `DLMF.Lame.lameUEk`, `DLMF.Lame.lameSEk`, `DLMF.Lame.lameCEk`,
  `DLMF.Lame.lameDEk`, `DLMF.Lame.lameSCEk`, `DLMF.Lame.lameSDEk`,
  `DLMF.Lame.lameCDEk`, `DLMF.Lame.lameSCDEk`
  ([source](DLMF/Lame/Polynomials/Basic.lean#L175)). This construction accepts
  complex z and is separate from the choice-defined real Ec/Es functions;
  identification on their common domain is a bridge theorem.

### §29.17 Other Solutions

- **Reduction-of-order second solution**, [DLMF 29.17.E1](https://dlmf.nist.gov/29.17.E1):
  F(z)=E(z)∫_(iK′)^zE(u)⁻²du is an explicit expression in
  `DLMF.Lame.lamePolyEk_second_solution`
  ([source](DLMF/Lame/OtherSolutions.lean#L36)), rather than a named function.
  Lean uses the straight segment from iK′ and assumes that its interior avoids
  zeros of E and other Jacobi poles. Different paths through singularities are
  not identified by this local construction.

- **Algebraic Lamé and Lamé–Wangerin classes**, [DLMF §29.17(ii)](https://dlmf.nist.gov/29.17.ii), [§29.17(iii)](https://dlmf.nist.gov/29.17.iii):
  Algebraic Lamé functions are solutions at half-odd-integer ν, algebraic in
  sn,cn,dn with primitive period 8K. Lamé–Wangerin functions are solutions for
  which (sn z)^(1/2)w(z) is bounded on the segment iK′ to 2K+iK′. These are
  prose definitions in DLMF, although the existing OtherSolutions module does
  not acquire them. No local named predicates or normalized constructions were
  found. They are distinct from the integer-order Lamé polynomials.

### §29.18 Mathematical Applications

- **Sphero-conal and ellipsoidal coordinate maps**, [DLMF 29.18.E2–3](https://dlmf.nist.gov/29.18.E2), [29.18.E8–9](https://dlmf.nist.gov/29.18.E8):
  The exact sphero-conal map is
  (x,y,z)=(kr snβ snγ, i(k/k′)r cnβ cnγ, (r/k′)dnβ dnγ), with r≥0,
  β=K+iβ′, 0≤β′≤2K′, 0≤γ≤4K. The ellipsoidal map is
  (k snα snβ snγ, −(k/k′)cnα cnβ cnγ, i/(kk′)dnα dnβ dnγ), with
  α=K+iK′−α′, 0≤α′<K, and the same β,γ ranges. No named Lean coordinate
  constructions were found. The separated equations reuse the spherical-Bessel,
  Lamé and Lamé-wave equations, rather than defining further special functions.

## Chapter 30 — Spheroidal wave functions

Expanded review: all 18 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§30.1–30.18 checked; matching headings are §§30.3(i),
30.4(i) and 30.11(i). Names below are in `DLMF.Spheroidal`.

### §30.1 Special Notation

- **Real squared parameter and Flammer conversion**, [DLMF §30.1](https://dlmf.nist.gov/30.1), [30.1.E1–2](https://dlmf.nist.gov/30.1.E1):
  γ² is an arbitrary real number, with m≥0 and n≥m integers. In Lean, γ2:ℝ
  retains its sign: positive is prolate, negative is oblate. Flammer's eigenvalue
  is λ_mn(γ)=λ_n^m(γ²)+γ², an expression rather than a separate eigenvalue
  construction; his radial R functions reuse the DLMF S functions.
  `DLMF.Spheroidal.flammerD`, `DLMF.Spheroidal.flammerS1` and
  `DLMF.Spheroidal.flammerS2`
  ([source](DLMF/Spheroidal/Basic/Ferrers.lean#L209)) implement the angular
  normalization, using the value at zero or derivative at zero according to
  n−m parity. The functions take γ², not an independently signed γ; second-kind
  existence restrictions are inherited by flammerS2.

  [DLMF 30.1.E1](https://dlmf.nist.gov/30.1.E1):
  **Flammer's angular function of the first kind** `S^{(1)}_{mn}(γ, x) = d_{mn}(γ) 𝖯s^m_n(x, γ²)`
  (DLMF 30.1.1), as a function of `γ²`.
  `DLMF.Spheroidal.flammerS1` ([definition](DLMF/Spheroidal/Basic/Ferrers.lean#L218)).

  [DLMF 30.1.E1](https://dlmf.nist.gov/30.1.E1):
  **Flammer's angular function of the second kind** `S^{(2)}_{mn}(γ, x) = d_{mn}(γ) 𝖰s^m_n(x, γ²)`
  (DLMF 30.1.1), as a function of `γ²`.
  `DLMF.Spheroidal.flammerS2` ([definition](DLMF/Spheroidal/Basic/Ferrers.lean#L223)).

  [DLMF 30.1.E2](https://dlmf.nist.gov/30.1.E2):
  **Flammer's normalization constant** `d_{mn}(γ)` (DLMF 30.1.2), a function of `γ²`: chosen so
  that `S^{(1)}_{mn}(γ, 0) = (-1)^m 𝖯^m_n(0)` for `n - m` even and
  `dS^{(1)}_{mn}(γ, x)/dx|_{x=0} = (-1)^m d𝖯^m_n(x)/dx|_{x=0}` for `n - m` odd.
  `DLMF.Spheroidal.flammerD` ([definition](DLMF/Spheroidal/Basic/Ferrers.lean#L209)).

### §30.2 Differential Equations

- **Equation, Liouville and scaled-variable forms**, [DLMF 30.2.E1–4](https://dlmf.nist.gov/30.2.E1):
  `DLMF.Spheroidal.IsSpheroidalSolutionOn` and
  `DLMF.Spheroidal.IsSpheroidalSolutionReal` encode the complex equation and
  its real interval form. `DLMF.Spheroidal.IsSpheroidalLiouvilleSolution` and
  `DLMF.Spheroidal.IsSpheroidalZetaSolution` encode the substitutions
  z=cos t, w=(1−z²)⁻¹ᐟ⁴g and ζ=γz
  ([source](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L80)). The substitutions and their powers
  are explicit expressions; equivalence requires compatible branches and
  exclusion of the singular points. ζ=γz is invertible only when γ≠0.

  [DLMF 30.2.E1](https://dlmf.nist.gov/30.2.E1):
  **The spheroidal differential equation** (DLMF 30.2.1)
  `d/dz((1-z²) dw/dz) + (λ + γ²(1-z²) - μ²/(1-z²)) w = 0` on a set `U` (to be taken open and
  avoiding `±1`), with complex parameters: `w` is differentiable at every point of `U` and
  `(1-z²) w'(z)` has derivative `-(λ + γ²(1-z²) - μ²/(1-z²)) w(z)` there.
  `DLMF.Spheroidal.IsSpheroidalSolutionOn` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L80)).

  [DLMF 30.2.E1](https://dlmf.nist.gov/30.2.E1):
  **The spheroidal differential equation on `(-1, 1)`** (DLMF 30.2.1 with `z = x` real and
  real parameters), for real-valued `f`: `f` is differentiable on `(-1, 1)` and `(1-x²) f'(x)` has
  derivative `-(λ + γ²(1-x²) - μ²/(1-x²)) f(x)` there.
  `DLMF.Spheroidal.IsSpheroidalSolutionReal` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L92)).

  [DLMF 30.2.E2](https://dlmf.nist.gov/30.2.E2):
  **The Liouville normal form** (DLMF 30.2.2)
  `g'' + (λ + 1/4 + γ² sin²t - (μ² - 1/4)/sin²t) g = 0` on a set `T` of complex `t` (to be taken
  open and free of zeros of `sin t`).
  `DLMF.Spheroidal.IsSpheroidalLiouvilleSolution` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L103)).

  [DLMF 30.2.E4](https://dlmf.nist.gov/30.2.E4):
  **The spheroidal equation in the variable `ζ = γz`** (DLMF 30.2.4)
  `(ζ² - γ²) w'' + 2ζ w' + (ζ² - λ - γ² - γ²μ²/(ζ² - γ²)) w = 0` on a set `V` (to be taken open and
  avoiding `±γ`); `γ2` stands for `γ²`.
  `DLMF.Spheroidal.IsSpheroidalZetaSolution` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L114)).

### §30.3 Eigenvalues

<!-- retained entry 227 -->
- **Eigenvalues λₙᵐ(γ²)**, [§30.3(i)](https://dlmf.nist.gov/30.3.i):
  `spheroidalSpectrum`, `spheroidalEigenvalue`, with
  `IsSpheroidalFactor`, in [Basic](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L151).
  Lean takes γ² as a real argument, allowing prolate and oblate cases.
  The choice uses the number n−m of smaller spectral values, with a zero
  fallback; `exists_spheroidalEigenvalue` and `spheroidalEigenvalue_spec`
  prove the characterization when m≤n in
  [Existence](DLMF/Spheroidal/Existence.lean#L60).

- **Entire-factor spectrum, ordered eigenvalue and continued-fraction parity**, [DLMF §30.3(i)](https://dlmf.nist.gov/30.3.i), [30.3.E5–7](https://dlmf.nist.gov/30.3.E5):
  `DLMF.Spheroidal.IsSpheroidalFactor`, `DLMF.Spheroidal.spheroidalSpectrum`
  and `DLMF.Spheroidal.spheroidalEigenvalue`
  ([source](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L151)) select the entire g in
  w=(1−x²)^(m/2)g(x), and the eigenvalue with exactly n−m smaller spectral
  values. The two α,β,γ coefficient triples are
  `DLMF.Spheroidal.spheroidalCFAlpha`, `DLMF.Spheroidal.spheroidalCFBeta`,
  `DLMF.Spheroidal.spheroidalCFGamma`, and the three corresponding Alt
  constructions `DLMF.Spheroidal.spheroidalCFAlphaAlt`,
  `DLMF.Spheroidal.spheroidalCFBetaAlt`, `DLMF.Spheroidal.spheroidalCFGammaAlt`
  ([source](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L226)). The fraction recursions advance
  by two, retaining the even/odd coefficient parity and β₀/β₁ terminal choice;
  the generic finite-tail expressions occur in theorem statements.

  [DLMF 30.3.E6](https://dlmf.nist.gov/30.3.E6):
  `α_k = -(k+1)(k+2)` (DLMF 30.3.6), the coefficients of the power-series recurrence 30.4.5.
  `DLMF.Spheroidal.spheroidalCFAlpha` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L226)).

  [DLMF 30.3.E6](https://dlmf.nist.gov/30.3.E6):
  `β_k = (m+k)(m+k+1) - γ²` (DLMF 30.3.6).
  `DLMF.Spheroidal.spheroidalCFBeta` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L230)).

  [DLMF 30.3.E6](https://dlmf.nist.gov/30.3.E6):
  `γ_k = γ²` (DLMF 30.3.6).
  `DLMF.Spheroidal.spheroidalCFGamma` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L234)).

  [DLMF 30.3.E7](https://dlmf.nist.gov/30.3.E7):
  `α_k = γ² (k+2m+1)(k+2m+2)/((2k+2m+3)(2k+2m+5))` (DLMF 30.3.7).
  `DLMF.Spheroidal.spheroidalCFAlphaAlt` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L238)).

  [DLMF 30.3.E7](https://dlmf.nist.gov/30.3.E7):
  `β_k = (k+m)(k+m+1) - 2γ² ((k+m)(k+m+1) - 1 + m²)/((2k+2m-1)(2k+2m+3))` (DLMF 30.3.7).
  `DLMF.Spheroidal.spheroidalCFBetaAlt` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L244)).

  [DLMF 30.3.E7](https://dlmf.nist.gov/30.3.E7):
  `γ_k = γ² (k-1)k/((2k+2m-3)(2k+2m-1))` (DLMF 30.3.7).
  `DLMF.Spheroidal.spheroidalCFGammaAlt` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L250)).

- **Taylor coefficients, convergence radius and eighth-order auxiliaries**, [DLMF 30.3.E8–12](https://dlmf.nist.gov/30.3.E8):
  `DLMF.Spheroidal.spheroidalEll` is the kth Taylor coefficient at t=0 of
  t↦λ_n^m(t), corresponding to ℓ_(2k)γ^(2k)
  ([source](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L296)).
  `DLMF.Spheroidal.spheroidalEllA`, `DLMF.Spheroidal.spheroidalEllB`,
  `DLMF.Spheroidal.spheroidalEllC`, `DLMF.Spheroidal.spheroidalEllD` are the
  exact rational auxiliaries in the ℓ₈ formula. The positive radius r_n^m is
  existential in `DLMF.Spheroidal.hasSum_spheroidalEll`
  ([source](DLMF/Spheroidal/Eigenvalues.lean#L158)), not a chosen maximal
  analytic convergence radius.

  [DLMF 30.3.E8](https://dlmf.nist.gov/30.3.E8):
  The coefficient `ℓ_{2k}` of `γ^{2k}` in the expansion 30.3.8 of `λ^m_n(γ²)`: the `k`-th
  Taylor coefficient at `0` of `γ² ↦ λ^m_n(γ²)`.
  `DLMF.Spheroidal.spheroidalEll` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L296)).

  [DLMF 30.3.E12](https://dlmf.nist.gov/30.3.E12):
  The auxiliary quantity `A` of DLMF 30.3.12 (entering `ℓ_8`, 30.3.11).
  `DLMF.Spheroidal.spheroidalEllA` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L302)).

  [DLMF 30.3.E12](https://dlmf.nist.gov/30.3.E12):
  The auxiliary quantity `B` of DLMF 30.3.12.
  `DLMF.Spheroidal.spheroidalEllB` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L312)).

  [DLMF 30.3.E12](https://dlmf.nist.gov/30.3.E12):
  The auxiliary quantity `C` of DLMF 30.3.12.
  `DLMF.Spheroidal.spheroidalEllC` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L324)).

  [DLMF 30.3.E12](https://dlmf.nist.gov/30.3.E12):
  The auxiliary quantity `D` of DLMF 30.3.12.
  `DLMF.Spheroidal.spheroidalEllD` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L334)).

### §30.4 Functions of the First Kind

<!-- retained entry 228 -->
- **Angular spheroidal function of the first kind Psₙᵐ**,
  [§30.4(i) and 30.4.1](https://dlmf.nist.gov/30.4.E1):
  `IsSpheroidalPsFactor`, `spheroidalPsFactor`, `spheroidalPs`,
  `spheroidalPsC` in [Basic](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L179).
  The selected analytic factor has the DLMF integral normalization and
  parity-dependent sign at zero. `spheroidalPs` is real on (−1,1);
  `spheroidalPsC` is the complex cut-plane version with explicit principal
  powers of z−1 and z+1. The factor's existence and uniqueness are proved
  by `existsUnique_isSpheroidalPsFactor` in
  [Existence](DLMF/Spheroidal/Existence.lean#L81).

- **Normalized entire factor, power coefficients and real angular function**, [DLMF 30.4.E1–5](https://dlmf.nist.gov/30.4.E1):
  `DLMF.Spheroidal.IsSpheroidalPsFactor`,
  `DLMF.Spheroidal.spheroidalPsFactor` and `DLMF.Spheroidal.spheroidalPs`
  ([source](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L179)) impose the integral
  ∫₋₁¹Ps²dx=2(n+m)!/((2n+1)(n−m)!) and the parity-dependent sign of Ps(0)
  or Ps′(0). The real angular wrapper is intended on [−1,1]. The g_k of its
  power expansion are Taylor-coefficient expressions of the chosen entire
  factor in `DLMF.Spheroidal.hasSum_spheroidalPs`
  ([source](DLMF/Spheroidal/Angular.lean#L637)), without a second independent
  coefficient family definition. `DLMF.Spheroidal.spheroidalExpansionCoeff`
  ([source](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L217)) is the normalized projection c_n
  of 30.4.8. The general expansion theorem is in L², with stronger pointwise
  or uniform statements requiring their additional hypotheses.

  [DLMF 30.4.E8](https://dlmf.nist.gov/30.4.E8):
  **Expansion coefficients** `c_n` of a function `f` in the functions `𝖯s^m_n(x, γ²)`
  (DLMF 30.4.8): `c_n = (n + 1/2) (n-m)!/(n+m)! ∫_{-1}^1 f(t) 𝖯s^m_n(t, γ²) dt`.
  `DLMF.Spheroidal.spheroidalExpansionCoeff` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L217)).

### §30.5 Functions of the Second Kind

- **Interval and cut-plane functions with distinct boundary values**, [DLMF 30.5.E1–4](https://dlmf.nist.gov/30.5.E1), [30.6.E1–5](https://dlmf.nist.gov/30.6.E1):
  `DLMF.Spheroidal.IsSpheroidalQs` and `DLMF.Spheroidal.spheroidalQs`
  characterize the interval second-kind function by its equation, opposite
  parity and normalized Wronskian. `DLMF.Spheroidal.spheroidalPsC` is the
  complex first kind, (−1)^m(z−1)^(m/2)(z+1)^(m/2)g(z), with separate principal
  powers ([source](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L210)).
  `DLMF.Spheroidal.spheroidalCutPlane`, `DLMF.Spheroidal.IsSpheroidalQsC`
  and `DLMF.Spheroidal.spheroidalQsC`
  ([source](DLMF/Spheroidal/Basic/Ferrers.lean#L157)) represent continuation from
  z>1 to ℂ\(−∞,1]. Upper/lower boundary values on (−1,1) have the factors
  (∓i)^m and, for second kind, the additional ∓iπPs/2 term. Hence the interval
  and continued functions cannot be identified by direct substitution on the
  cut. Outside-domain zeros and choice fallbacks are implementation conventions.
  Second-kind existence has the forward-recursion restriction of §30.8(ii).

  [DLMF 30.5.E1](https://dlmf.nist.gov/30.5.E1):
  **Characterization of `𝖰s^m_n(x, γ²)`** (DLMF 30.5.1, 30.5.2, 30.5.4): a solution of 30.2.1
  on `(-1, 1)` with `μ = m`, `λ = λ^m_n(γ²)`, of parity `(-1)^{n-m+1}`, whose Wronskian with
  `𝖯s^m_n` is `(n+m)!/((1-x²)(n-m)!) A^m_n(γ²) A^{-m}_n(γ²)`; it vanishes off `(-1, 1)`.
  `DLMF.Spheroidal.IsSpheroidalQs` ([definition](DLMF/Spheroidal/Basic/Ferrers.lean#L133)).

  [DLMF 30.5.E1](https://dlmf.nist.gov/30.5.E1):
  **The spheroidal wave function of the second kind** `𝖰s^m_n(x, γ²)` (DLMF 30.5.1), for
  `-1 < x < 1`, defined by choice from its characterization `IsSpheroidalQs` (junk `0` if it did
  not exist).
  `DLMF.Spheroidal.spheroidalQs` ([definition](DLMF/Spheroidal/Basic/Ferrers.lean#L150)).

### §30.6 Functions of Complex Argument

- **Spheroidal power-series coefficients and summability conditions**, [DLMF 30.6.E1](https://dlmf.nist.gov/30.6.E1):
  **Characterization of `𝑄s^m_n(z, γ²)`** (DLMF 30.6.1, 30.6.5): a solution of 30.2.1 on
  `ℂ ∖ (-∞, 1]` with `μ = m`, `λ = λ^m_n(γ²)`, whose boundary values from the upper half plane on
  `(-1, 1)` are `(-i)^m (𝖰s^m_n(x, γ²) - (iπ/2) 𝖯s^m_n(x, γ²))`; it vanishes on `(-∞, 1]`.
  `DLMF.Spheroidal.IsSpheroidalQsC` ([definition](DLMF/Spheroidal/Basic/Ferrers.lean#L160)).

  [DLMF 30.6.E1](https://dlmf.nist.gov/30.6.E1):
  **The spheroidal wave function of the second kind of complex argument** `𝑄s^m_n(z, γ²)`
  (DLMF 30.6.1), for `z ∈ ℂ ∖ (-∞, 1]`, defined by choice from `IsSpheroidalQsC` (junk `0` if it
  did not exist).
  `DLMF.Spheroidal.spheroidalQsC` ([definition](DLMF/Spheroidal/Basic/Ferrers.lean#L173)).

### §30.8 Expansions in Series of Ferrers Functions

- **Integral coefficients, negative order and finite lower-index extension**, [DLMF 30.8.E1–6](https://dlmf.nist.gov/30.8.E1), [§30.8(ii)](https://dlmf.nist.gov/30.8.ii):
  R=⌊(n−m)/2⌋ and N=⌊(n+m)/2⌋ are index expressions.
  `DLMF.Spheroidal.spheroidalCoeffMain` implements the integral defining
  a_n,k^m for k≥−R. `DLMF.Spheroidal.spheroidalCoeff` adds forward continuation
  down to −N and zero values below −N; `DLMF.Spheroidal.spheroidalCoeffNeg`
  implements a_n,k^(−m) by factorial rescaling for k≥−R
  ([source](DLMF/Spheroidal/Basic/Ferrers.lean#L60)).
  `DLMF.Spheroidal.spheroidalRecA`, `DLMF.Spheroidal.spheroidalRecB`,
  `DLMF.Spheroidal.spheroidalRecC` and `DLMF.Spheroidal.spheroidalFwd`
  ([source](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L255)) supply A_k,B_k,C_k and the forward
  sequence with f_(−N−1)=0,f_(−N)=1. If f_(−R)=0, DLMF leaves the extension
  below −R undefined and states that Qs does not exist. Lean's division by the
  matching value and its totalized fallback do not supply that missing function.

  [DLMF 30.8.E3](https://dlmf.nist.gov/30.8.E3):
  `A_k = -γ² (n-m+2k-1)(n-m+2k)/((2n+4k-3)(2n+4k-1))` (DLMF 30.8.3), `k ∈ ℤ`.
  `DLMF.Spheroidal.spheroidalRecA` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L255)).

  [DLMF 30.8.E3](https://dlmf.nist.gov/30.8.E3):
  `B_k = (n+2k)(n+2k+1) - 2γ² ((n+2k)(n+2k+1) - 1 + m²)/((2n+4k-1)(2n+4k+3))`
  (DLMF 30.8.3), `k ∈ ℤ`.
  `DLMF.Spheroidal.spheroidalRecB` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L261)).

  [DLMF 30.8.E3](https://dlmf.nist.gov/30.8.E3):
  `C_k = -γ² (n+m+2k+1)(n+m+2k+2)/((2n+4k+3)(2n+4k+5))` (DLMF 30.8.3), `k ∈ ℤ`.
  `DLMF.Spheroidal.spheroidalRecC` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L269)).

  [DLMF 30.8.ii](https://dlmf.nist.gov/30.8.ii):
  The forward solution of the recurrence 30.8.4 used in DLMF §30.8(ii): with
  `N = ⌊(n+m)/2⌋`, `spheroidalFwd n m γ2 j = f_{j-N-1}` where `f_{-N-1} = 0`, `f_{-N} = 1` and
  `A_k f_{k-1} + (B_k - λ^m_n(γ²)) f_k + C_k f_{k+1} = 0`.
  `DLMF.Spheroidal.spheroidalFwd` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L275)).

- **Recessive negative tail and parity-dependent matching constant**, [DLMF 30.8.E9–11](https://dlmf.nist.gov/30.8.E9):
  `DLMF.Spheroidal.IsSpheroidalCoeffPrime` and
  `DLMF.Spheroidal.spheroidalCoeffPrime`
  ([source](DLMF/Spheroidal/Basic/Ferrers.lean#L99)) specify the recessive a′
  coefficients for k≤−N−1 through the recurrence and matching equation.
  `DLMF.Spheroidal.spheroidalCPrime`
  ([source](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L288)) is C′=γ²/(4m²−1) for n−m even,
  and −γ²/((2m−1)(2m−3)) for n−m odd. The recessive-tail construction and
  existence statement are separate from the directly integrated main coefficients.

  [DLMF 30.8.E9](https://dlmf.nist.gov/30.8.E9):
  `a'^m_{n,k}(γ²)` (DLMF §30.8(ii)), defined by choice (junk `0` if it did not exist).
  `DLMF.Spheroidal.spheroidalCoeffPrime` ([definition](DLMF/Spheroidal/Basic/Ferrers.lean#L126)).

  [DLMF 30.8.E10](https://dlmf.nist.gov/30.8.E10):
  **The recessive coefficients** `a'^m_{n,k}(γ²)`, `k ≤ -N - 1` (DLMF §30.8(ii)): a solution
  of 30.8.4 for `k ≤ -N - 2` that is recessive as `k → -∞` (negligible against every solution not
  proportional to it), normalized by 30.8.10 with `C'` from 30.8.11; extended by `0` for
  `k ≥ -N`.
  `DLMF.Spheroidal.IsSpheroidalCoeffPrime` ([definition](DLMF/Spheroidal/Basic/Ferrers.lean#L99)).

  [DLMF 30.8.E11](https://dlmf.nist.gov/30.8.E11):
  The constant `C'` of DLMF 30.8.11: `γ²/(4m²-1)` for `n - m` even and
  `-γ²/((2m-1)(2m-3))` for `n - m` odd.
  `DLMF.Spheroidal.spheroidalCPrime` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L288)).

### §30.9 Asymptotic Approximations and Expansions

- **Prolate and oblate scales with six displayed coefficients**, [DLMF 30.9.E1–6](https://dlmf.nist.gov/30.9.E1):
  The prolate q=2(n−m)+1 is an expression;
  `DLMF.Spheroidal.spheroidalOblateQ` is n+1 when n−m is even and n otherwise.
  `DLMF.Spheroidal.spheroidalProlateBeta` and
  `DLMF.Spheroidal.spheroidalOblateC`
  ([source](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L343)) contain exactly β₀,…,β₅ and
  c₀,…,c₅, respectively. Both return zero at larger indices; those zeros are
  not DLMF's further coefficients. The asymptotic theorems quantify an all-order
  sequence agreeing at these first six indices; no independent complete
  coefficient sequence is defined.

  [DLMF 30.9.E2](https://dlmf.nist.gov/30.9.E2):
  The coefficients `β_0, …, β_5` of the prolate expansion 30.9.1 (DLMF 30.9.2, 30.9.3), with
  `q = 2(n-m)+1`; `0` for `j ≥ 6` (not given by DLMF).
  `DLMF.Spheroidal.spheroidalProlateBeta` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L343)).

  [DLMF 30.9.ii](https://dlmf.nist.gov/30.9.ii):
  The parameter `q` of the oblate expansion 30.9.4: `n + 1` for `n - m` even, `n` for `n - m`
  odd.
  `DLMF.Spheroidal.spheroidalOblateQ` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L362)).

  [DLMF 30.9.E5](https://dlmf.nist.gov/30.9.E5):
  The coefficients `c_0, …, c_5` of the oblate expansion 30.9.4 (DLMF 30.9.5, 30.9.6); `0` for
  `j ≥ 6` (not given by DLMF).
  `DLMF.Spheroidal.spheroidalOblateC` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L367)).

### §30.11 Radial Spheroidal Wave Functions

<!-- retained entry 229 -->
- **Cylinder choices Cν⁽ʲ⁾ and spherical functions ψₖ⁽ʲ⁾**,
  [30.11.1–2](https://dlmf.nist.gov/30.11.E1): `spheroidalCylinder`,
  `spheroidalPsi` in [Basic](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L388), dispatching
  to J, Y and the two Hankel functions. ψ⁽¹⁾ uses the entire spherical-J
  construction; ψ⁽²⁾, ψ⁽³⁾, ψ⁽⁴⁾ use the explicit square-root factors and
  inherit their branch and zero restrictions.

- **Four cylinder families and spherical-Bessel building blocks**, [DLMF 30.11.E1–2](https://dlmf.nist.gov/30.11.E1):
  `DLMF.Spheroidal.spheroidalCylinder` selects J,Y,H¹,H² and
  `DLMF.Spheroidal.spheroidalPsi` supplies ψ_k^j(z)=√(π/(2z))C_(k+1/2)^j(z)
  ([source](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L388)). For j=1, Lean uses the entire
  `DLMF.sphericalJ`, whose agreement with that principal quotient is asserted
  off the negative real cut. The other three use the principal square root;
  their branch conventions and j∈{1,2,3,4} must be retained.

<!-- retained entry 230 -->
- **Radial spheroidal functions Sₙᵐ⁽ʲ⁾ and normalization Aₙ±ᵐ**,
  [30.11.3–4](https://dlmf.nist.gov/30.11.E3): `spheroidalRadial`,
  `spheroidalA`, `spheroidalANeg`, with `spheroidalCoeffMain`,
  `spheroidalCoeff`, `spheroidalCoeffNeg`, in
  [FerrersDefs](DLMF/Spheroidal/Basic/Ferrers.lean#L60).
  This is an actual bilateral spherical-Bessel series, using the angular
  expansion coefficients. γ is complex, but the implementation uses
  `(γ ^ 2).re` for coefficients, so the intended γ² must be real.

- **Radial coefficient sums and joining factors**, [DLMF 30.11.E3–4](https://dlmf.nist.gov/30.11.E3), [30.11.E8–12](https://dlmf.nist.gov/30.11.E8):
  `DLMF.Spheroidal.spheroidalA`, `DLMF.Spheroidal.spheroidalANeg` are the
  alternating coefficient sums A_n^±m with their different lower limits.
  `DLMF.Spheroidal.spheroidalRadial` is the Bessel-series construction of all
  four S_n^(m,j); `DLMF.Spheroidal.spheroidalK` gives the parity-dependent
  joining factor K_n^m through the first coefficient and the angular value
  or derivative at zero ([source](DLMF/Spheroidal/Basic/Ferrers.lean#L182)).
  The radial parameter γ is complex with γ² real, evaluated in coefficient
  functions as (γ²).re; this hypothesis is essential. The series domains are
  z≠0 for j=1 and |z|>1 for j=2,3,4, with principal-power analyticity
  restrictions in the equation theorems. The integral formula 30.11.12 is
  `DLMF.Spheroidal.spheroidalRadial_one_integral`
  ([source](DLMF/Spheroidal/Radial.lean#L217)), a representation of this
  series-defined function, without a second named integral construction.

  [DLMF 30.11.E10](https://dlmf.nist.gov/30.11.E10):
  **The factor** `K^m_n(γ)` of 30.11.8 (DLMF 30.11.10 for `n - m` even, 30.11.11 for `n - m`
  odd), `γ²` real (evaluated at `(γ^2).re`).
  `DLMF.Spheroidal.spheroidalK` ([definition](DLMF/Spheroidal/Basic/Ferrers.lean#L192)).

### §30.12 Generalized and Coulomb Spheroidal Functions

- **Two generalized differential equations**, [DLMF 30.12.E1–2](https://dlmf.nist.gov/30.12.E1):
  `DLMF.Spheroidal.IsGenSpheroidalSolutionOn` adds αz to the potential;
  `DLMF.Spheroidal.IsSpheroidalSolutionOn₂` adds −α(α+1)/z²
  ([source](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L127)). The first equation includes
  Coulomb spheroidal functions. These predicates define solution classes;
  no separately normalized generalized/Coulomb family was found locally.

  [DLMF 30.12.E1](https://dlmf.nist.gov/30.12.E1):
  **Generalized spheroidal wave equation** (DLMF 30.12.1)
  `d/dz((1-z²) w') + (λ + αz + γ²(1-z²) - μ²/(1-z²)) w = 0` on `U`; Coulomb spheroidal
  functions are solutions.
  `DLMF.Spheroidal.IsGenSpheroidalSolutionOn` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L127)).

  [DLMF 30.12.E2](https://dlmf.nist.gov/30.12.E2):
  **The second generalization** (DLMF 30.12.2)
  `d/dz((1-z²) w') + (λ + γ²(1-z²) - α(α+1)/z² - μ²/(1-z²)) w = 0` on `U` (to be taken open and
  avoiding `0, ±1`).
  `DLMF.Spheroidal.IsSpheroidalSolutionOn₂` ([definition](DLMF/Spheroidal/Basic/EquationAndSpectralData.lean#L138)).

### §30.13 Wave Equation in Prolate Spheroidal Coordinates

- **Prolate and oblate coordinate charts, metrics and Laplacians**, [DLMF 30.13.E1–6](https://dlmf.nist.gov/30.13.E1), [30.14.E1–6](https://dlmf.nist.gov/30.14.E1):
  For c>0, the prolate map is
  (x,y,z)=(c√((ξ²−1)(1−η²))cosφ,c√((ξ²−1)(1−η²))sinφ,cξη), with ξ>1,
  −1<η<1, 0≤φ<2π. The oblate map replaces ξ²−1 by ξ²+1 and uses ξ>0;
  the focal disk and axis are excluded from this chart. DLMF also defines the
  metric coefficients h_ξ,h_η,h_φ and the coordinate forms of the Laplacian.
  No named local constructions of these maps, metric coefficients or operators
  were found. The separation parameters γ²=κ²c²≥0 and γ²=−κ²c²≤0 reuse the
  existing angular/radial spheroidal functions. The Dirichlet eigenvalue
  conditions 30.13.15–16 and 30.14.9 are zero equations for those functions;
  there is no additional chosen sequence of cavity eigenvalues.

### §30.15 Signal Analysis

- **Scaled functions and concentration eigenvalues**, [DLMF 30.15.E1–2](https://dlmf.nist.gov/30.15.E1):
  For τ,σ>0 and γ=τσ,
  φ_n(t)=√((2n+1)/(2τ))√Λ_n Ps_n^0(t/τ,γ²), with
  Λ_n=(2γ/π)(K_n^0(γ)A_n^0(γ²))². No separately named Lean φ_n or Λ_n
  construction was found. The definition is for real t on the whole line.
  The existing `DLMF.Spheroidal.spheroidalPsFactor` supplies the entire
  order-zero continuation: for m=0, the real wrapper
  `DLMF.Spheroidal.spheroidalPs` reduces to this factor's real part even
  outside [−1,1]. Thus the displayed scaling is expressible with the existing
  constructions, despite the absence of a dedicated φ_n name.

- **Interval indicator, band limitation and extremal energy functional**, [DLMF 30.15.E6](https://dlmf.nist.gov/30.15.E6), [30.15.E9–13](https://dlmf.nist.gov/30.15.E9):
  χ_σ is the indicator of [−σ,σ], including endpoints. “σ-bandlimited” means
  that the Fourier transform vanishes off this interval. The band-energy
  functional is β(f)=(1/(2π))∫₋σ^σ|∫ℝe^(−itω)f(t)dt|²dω; B is its supremum
  over unit L² functions with time-interval energy α. The maximizing
  representative is aφ₀χ_τ+bφ₀(1−χ_τ), where a=√(α/Λ₀),
  b=√((1−α)/(1−Λ₀)), when Λ₀<α≤1; B=1 for 0<α≤Λ₀. No local named
  spheroidal energy/optimization constructions were found. General indicators
  and Fourier support conditions express parts of the definitions, but do not
  constitute these selected spheroidal objects. These are exact mathematical
  definitions, independent of any numerical signal-processing implementation.

### §30.16 Methods of Computation

- **Exact finite spectral truncations and eigenvector normalization**, [DLMF 30.16.E1–3](https://dlmf.nist.gov/30.16.E1), [30.16.E6–9](https://dlmf.nist.gov/30.16.E6):
  DLMF defines a d×d parity-dependent tridiagonal matrix A, its ordered
  eigenvalues α_(j,d), and normalized eigenvectors e_(j,d) whose limits recover
  λ_n^m, a_n,k^m and Ps_n^m. The indexing is one-based, with
  p=⌊(n−m)/2⌋+1. The weighted quadratic normalization 30.16.7 fixes the
  eigenvector magnitude, requiring a compatible sign choice for its coefficient
  limit. No named local finite matrix, selected eigenvalue or eigenvector
  family was found. These exact constructions are recorded as gaps; the
  decimal eigenvalue example 30.16.5 and subsequent tables/software are
  excluded numerical material.

## Chapter 31 — Heun functions

Expanded review: all 18 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§31.1–31.18 checked; matching headings are §§31.14(i)
and 31.15(i). Fundamental Heun objects under other headings are included
explicitly as complementary entries. Names below are in `DLMF.Heun`.

### §31.1 Special Notation

- **Parameter roles and function notation**, [DLMF 31.1](https://dlmf.nist.gov/31.1):
  The notation distinguishes singularity a, accessory parameter q, exponent parameters α,β,γ,δ,ε and path-multiplier exponent ν. The chapter’s baseline |a|≥1,a≠1 is narrower than the total parameter space of the Lean definitions; singular choices need the hypotheses of each bridge. Merely suppressing parameters in Hℓ/Hf/Hp does not introduce additional functions.

### §31.2 Differential Equations

<!-- retained entry 231 -->
- **General Heun equation and normalized local solution Hℓ**,
  [31.2.1 and 31.3.1](https://dlmf.nist.gov/31.2.E1): `heunEps`,
  `heunCoeffP`, `heunCoeffR`, `IsHeunSolOn`, `heunODECoeff`,
  `heunLocalCoeff`, `heunLocalRadius`, `heunLocal` in
  [Basic](DLMF/Heun/Basic.lean#L66). The last is the native power series
  around zero, with the coefficient of degree zero normalized to one.
  `IsHeunFunctionOn`, `IsHeunEigenvalue01`, `heunFunction01` in
  [Basic](DLMF/Heun/Basic.lean#L157) describe solutions analytic at two
  finite singularities and choose a continuation on a specified disk;
  they do not select a global branch at all singularities or at infinity.
  The chosen disk continuation still depends on admitted
  `IsHeunEigenvalue01.analyticOn_ball` in
  [HeunFunctions](DLMF/Heun/HeunFunctions.lean#L50).
  `heunPoly` in [Basic](DLMF/Heun/Basic.lean#L212) is a finite polynomial
  with q supplied as a parameter, not a separately selected eigenvalue.

- **Normal, trigonometric and doubly periodic coordinate forms**, [DLMF 31.2.E2](https://dlmf.nist.gov/31.2.E2):
  The normal-form factor z^{−γ/2}(z−1)^{−δ/2}(z−a)^{−ε/2}, trigonometric z=sin²θ, Jacobi z=sn²ζ and Weierstrass shifts of 31.2.5–12 are substitutions in the equation, with branch choices for their powers. The normal coefficient objects are listed here; b₀,…,b₃,H of the elliptic form are explicit parameter expressions, without separately selected local coordinate maps or solution functions.

- **DLMF 31.2.3: the right-hand side coefficient of the normal form**, [DLMF 31.2.E3](https://dlmf.nist.gov/31.2.E3):
  DLMF 31.2.3: the right-hand side coefficient of the normal form
  `W'' = (A/z + B/(z-1) + C/(z-a) + D/z² + E/(z-1)² + F/(z-a)²) W`.
  `DLMF.Heun.heunNormalCoeff` ([definition](DLMF/Heun/Basic.lean#L110)).

- **Heun normal-form coefficients**, [DLMF 31.2.E4](https://dlmf.nist.gov/31.2.E4):
  DLMF 31.2.4: the coefficient `A` of the normal form (31.2.3).
  `DLMF.Heun.heunNormalA` ([definition](DLMF/Heun/Basic.lean#L91)).

  [DLMF 31.2.E4](https://dlmf.nist.gov/31.2.E4):
  DLMF 31.2.4: the coefficient `B` of the normal form (31.2.3).
  `DLMF.Heun.heunNormalB` ([definition](DLMF/Heun/Basic.lean#L95)).

  [DLMF 31.2.E4](https://dlmf.nist.gov/31.2.E4):
  DLMF 31.2.4: the coefficient `C` of the normal form (31.2.3).
  `DLMF.Heun.heunNormalC` ([definition](DLMF/Heun/Basic.lean#L100)).

  [DLMF 31.2.E4](https://dlmf.nist.gov/31.2.E4):
  DLMF 31.2.4: the coefficients `D, E, F` of the normal form, `D = ½γ(½γ - 1)` (with `γ`
  replaced by `δ`, `ε` for `E`, `F`).
  `DLMF.Heun.heunNormalD` ([definition](DLMF/Heun/Basic.lean#L105)).

- **F-homotopic, homographic and composite automorphisms**, [DLMF 31.2.v](https://dlmf.nist.gov/31.2.v):
  The exponent-changing prefactors and fractional-linear variable changes define the 8×24=192 Heun automorphisms. The project states these transformations through equations and parameter substitutions; no separate generic automorphism-group or transformed-parameter structure is constructed.

### §31.3 Basic Solutions

- **Heun recurrence coefficient polynomials**, [DLMF 31.3.E4](https://dlmf.nist.gov/31.3.E4):
  DLMF 31.3.4: `P_j = (j - 1 + α)(j - 1 + β)`.
  `DLMF.Heun.heunRecP` ([definition](DLMF/Heun/Basic.lean#L120)).

  [DLMF 31.3.E4](https://dlmf.nist.gov/31.3.E4):
  DLMF 31.3.4: `Q_j = j((j - 1 + γ)(1 + a) + aδ + ε)`, with `ε = α + β + 1 - γ - δ`.
  `DLMF.Heun.heunRecQ` ([definition](DLMF/Heun/Basic.lean#L124)).

  [DLMF 31.3.E4](https://dlmf.nist.gov/31.3.E4):
  DLMF 31.3.4: `R_j = a(j + 1)(j + γ)`.
  `DLMF.Heun.heunRecR` ([definition](DLMF/Heun/Basic.lean#L129)).

- **Eight local Frobenius solutions and their equivalent expressions**, [DLMF 31.3.E5](https://dlmf.nist.gov/31.3.E5):
  The second solution at zero and the six solutions at 1,a,∞ are products/compositions of the same `DLMF.Heun.heunLocal` ([source](DLMF/Heun/Basic.lean#L147)) with transformed parameters. They are bridge expressions, not independent native series objects. Integer-exponent resonances may require logarithmic solutions and are not supplied by an arbitrary division-based recurrence at its zero denominators.

### §31.4 Solutions Analytic at Two Singularities: Heun Functions

- **Two-singularity Heun families and accessory spectra**, [DLMF 31.4.E1](https://dlmf.nist.gov/31.4.E1):
  `DLMF.Heun.IsHeunFunctionOn` ([source](DLMF/Heun/Basic.lean#L157)), `DLMF.Heun.IsHeunEigenvalue01` ([source](DLMF/Heun/Basic.lean#L166)), `DLMF.Heun.heunFunction01` ([source](DLMF/Heun/Basic.lean#L175)), `DLMF.Heun.heunCFTail` ([source](DLMF/Heun/Basic.lean#L187)) supplement the normalized local series with analytic-at-two-points data, the 0–1 eigenvalue predicate, a chosen disk continuation and finite fraction tails. No globally enumerated qₘ or canonical function for every pair involving ∞ is selected. The disk continuation’s characterization still uses the admission recorded in the retained entry.

- **Finite Heun continued-fraction convergents**, [DLMF 31.4.E2](https://dlmf.nist.gov/31.4.E2):
  DLMF 31.4.2: the `m`-th approximant of the continued fraction
  `aγP₁/(Q₁ + q - R₁P₂/(Q₂ + q - R₂P₃/(Q₃ + q - ⋯)))`.
  `DLMF.Heun.heunCFApprox` ([definition](DLMF/Heun/Basic.lean#L194)).

### §31.5 Solutions Analytic at Three Singularities: Heun Polynomials

- **Heun polynomial eigenvalue matrix**, [DLMF 31.5.E1](https://dlmf.nist.gov/31.5.E1):
  DLMF 31.5.1: the `(n+1) × (n+1)` tridiagonal matrix with first row `(0, aγ, 0, …)` and row
  `j ≥ 1` equal to `(…, P_j, -Q_j, R_j, …)` (columns `j - 1, j, j + 1`), for `α = -n`. Its
  eigenvalues are the `q_{n,m}`, `m = 0, …, n`.
  `DLMF.Heun.heunPolyMatrix` ([definition](DLMF/Heun/Basic.lean#L200)).

- **Heun polynomial parameter versus eigenvalue index**, [DLMF 31.5.E2](https://dlmf.nist.gov/31.5.E2):
  The finite `DLMF.Heun.heunPoly` ([source](DLMF/Heun/Basic.lean#L212)) takes q directly, while `DLMF.Heun.heunPolyMatrix` ([source](DLMF/Heun/Basic.lean#L200)) gives the matrix whose eigenvalues are DLMF’s qₙ,ₘ. There is no separate definition choosing or ordering the complex accessory eigenvalues qₙ,ₘ; polynomial termination requires the corresponding spectral condition.

### §31.6 Path-Multiplicative Solutions

- **Path-multiplicative transformation condition**, [DLMF 31.6.E1](https://dlmf.nist.gov/31.6.E1):
  DLMF 31.6.1: `w` is path-multiplicative with exponent `ν` along the closed path `γ`: the
  analytic continuation of the germ of `w` at `γ 0` along `γ` returns as `e^{2νπi} w`. DLMF takes
  for `γ` a simple closed contour encircling the two singularities `s₁, s₂ ∈ {0, 1, a}` once in the
  positive sense but not the third; that choice is left to the user of the predicate.
  `DLMF.Heun.IsPathMultiplicative` ([definition](DLMF/Heun/Basic.lean#L316)).

### §31.8 Solutions via Quadratures

- **Hermite–Darboux quadratures and spectral curve**, [DLMF 31.8.E2](https://dlmf.nist.gov/31.8.E2):
  The quadrature solutions w±, product-polynomial Ψg,N, genus g of 31.8.3 and hyperelliptic curve ν²=∏(λ−λⱼ) are new mathematical objects here. Their ν is unrelated to the path-multiplier ν of §31.6. No general local construction selects Ψ, its spectral branch points, the curve or these quadrature solutions; explicit examples 31.8.4–5 are formulas only.

### §31.9 Orthogonality

- **Pochhammer contour, continued branch and normalization integral**, [DLMF 31.9.E2](https://dlmf.nist.gov/31.9.E2):
  `DLMF.Heun.localBranchCpow` ([source](DLMF/Heun/Basic.lean#L289)), `DLMF.Heun.pochhammerLoop` ([source](DLMF/Heun/Basic.lean#L294)), `DLMF.Heun.continuedPathIntegral` ([source](DLMF/Heun/Basic.lean#L306)) construct a principal-initial local power germ, a four-circle representative of the double loop and its analytically continued integral. The integral falls back to zero if continuation does not exist; it is not obtained by evaluating principal powers independently around the loop. The Wronskian normalization θₘ in 31.9.3 is an expression in supplied solutions. The two-variable weight ρ(s,t) of 31.9.6 is a local expression, distinct from the one-variable weight used below.

### §31.10 Integral Equations and Representations

- **Heun bilinear weight**, [DLMF 31.10.E2](https://dlmf.nist.gov/31.10.E2):
  DLMF 31.10.2: the weight `ρ(t) = t^{γ-1}(t-1)^{δ-1}(t-a)^{ε-1}` with principal powers (any
  other branch is a constant multiple).
  `DLMF.Heun.heunWeight` ([definition](DLMF/Heun/Basic.lean#L335)).

- **DLMF 31.10.4: Heun's operator**, [DLMF 31.10.E4](https://dlmf.nist.gov/31.10.E4):
  DLMF 31.10.4: Heun's operator
  `𝒟_z = z(z-1)(z-a) d²/dz² + (γ(z-1)(z-a) + δz(z-a) + εz(z-1)) d/dz + αβz`. Heun's equation is
  `𝒟_z w = q w`.
  `DLMF.Heun.heunOperator` ([definition](DLMF/Heun/Basic.lean#L327)).

- **Heun bilinear concomitant coefficient**, [DLMF 31.10.E6](https://dlmf.nist.gov/31.10.E6):
  DLMF 31.10.6: `p(t) = t^γ (t-1)^δ (t-a)^ε = t(t-1)(t-a)ρ(t)`, principal powers.
  `DLMF.Heun.heunConcomitantP` ([definition](DLMF/Heun/Basic.lean#L341)).

- **Heun integral kernels and separation coordinates**, [DLMF 31.10.E7](https://dlmf.nist.gov/31.10.E7):
  The θ,φ coordinates of 31.10.7, product P-symbol kernel 31.10.9 and explicit hypergeometric kernels 31.10.10–11 are formula constructions in the integral-representation statements, not independently named general local functions. Integral-equation eigenvalues κₘ and normalization constants are supplied data. The existing `DLMF.Heun.heunOperator` ([source](DLMF/Heun/Basic.lean#L327)) is the differential operator entering their kernel PDE.

- **Double-integral weight, Cartesian/spherical kernels and separation constants**, [DLMF 31.10.E13](https://dlmf.nist.gov/31.10.E13):
  The two-variable ρ(s,t), u,v,w of 31.10.17, cylinder-product kernel 31.10.19, spherical variables and P-symbol kernel of 31.10.20–23 introduce additional explicit expressions. No local object selects these kernels or the quadratic-root parameters m,p,a,b,a′,b′. Their independent separation constants and root/branch choices are not fixed by the single principal-power `heunWeight`.

### §31.11 Expansions in Series of Hypergeometric Functions

- **Heun hypergeometric recurrence coefficient P₅**, [DLMF 31.11.E3_1](https://dlmf.nist.gov/31.11.E3_1):
  DLMF 31.11.3_1 (added in DLMF 1.1.7): the Fuchs–Frobenius solution at `∞` of the P-symbol
  31.11.2, `P_j^5 = (λ)_j(1-γ+λ)_j/(1+λ-μ)_{2j} z^{-λ-j} ₂F₁(λ+j, 1-γ+λ+j; 1+λ-μ+2j; 1/z)`
  (principal power, `|z| > 1`).
  `DLMF.Heun.heunHypP5` ([definition](DLMF/Heun/Basic.lean#L256)).

- **Heun hypergeometric recurrence coefficient P₆**, [DLMF 31.11.E3_2](https://dlmf.nist.gov/31.11.E3_2):
  DLMF 31.11.3_2 (added in DLMF 1.1.7): the other Fuchs–Frobenius solution at `∞`,
  `P_j^6 = (λ-μ)_{2j}/((1-μ)_j(γ-μ)_j) z^{-μ+j} ₂F₁(μ-j, 1-γ+μ-j; 1-λ+μ-2j; 1/z)`.
  `DLMF.Heun.heunHypP6` ([definition](DLMF/Heun/Basic.lean#L265)).

- **Hypergeometric expansion coefficients and Type I/II choices**, [DLMF 31.11.E4](https://dlmf.nist.gov/31.11.E4):
  `DLMF.Heun.heunHypCoeff` ([source](DLMF/Heun/Basic.lean#L246)), `DLMF.Heun.heunHypCFTail` ([source](DLMF/Heun/Basic.lean#L273)) give the normalized forward coefficient recurrence and finite continued-fraction tails. The Type I and four Type II λ,μ choices specialize these same objects; the convergence ellipse has foci 0,1 through a and is a domain condition, without a separately named local ellipse. The full expansion is a representation theorem, not an additional globally continued Heun definition.

- **DLMF 31.11.6 (as corrected in DLMF 1.1.7)**, [DLMF 31.11.E6](https://dlmf.nist.gov/31.11.E6):
  DLMF 31.11.6 (as corrected in DLMF 1.1.7):
  `K_j = (j+α-μ-1)(j+β-μ-1)(j+γ-μ-1)(j-μ)/((2j+λ-μ-1)(2j+λ-μ-2))`; `j` is complex so that
  `j = -1` is allowed.
  `DLMF.Heun.heunHypK` ([definition](DLMF/Heun/Basic.lean#L221)).

- **Heun hypergeometric-expansion scale L**, [DLMF 31.11.E7](https://dlmf.nist.gov/31.11.E7):
  DLMF 31.11.7: `L_j = a(λ+j)(μ-j) - q + (j+α-μ)(j+β-μ)(j+γ-μ)(j+λ)/((2j+λ-μ)(2j+λ-μ+1))
  + (j-α+λ)(j-β+λ)(j-γ+λ)(j-μ)/((2j+λ-μ)(2j+λ-μ-1))`.
  `DLMF.Heun.heunHypL` ([definition](DLMF/Heun/Basic.lean#L229)).

- **DLMF 31.11.8 (as corrected in DLMF 1.1.7)**, [DLMF 31.11.E8](https://dlmf.nist.gov/31.11.E8):
  DLMF 31.11.8 (as corrected in DLMF 1.1.7):
  `M_j = (j-α+λ+1)(j-β+λ+1)(j-γ+λ+1)(j+λ)/((2j+λ-μ+1)(2j+λ-μ+2))`.
  `DLMF.Heun.heunHypM` ([definition](DLMF/Heun/Basic.lean#L239)).

- **Heun hypergeometric continued-fraction convergents**, [DLMF 31.11.E13](https://dlmf.nist.gov/31.11.E13):
  DLMF 31.11.13: the `m`-th approximant of
  `L₀/M₀ - (K₁/M₁)/(L₁/M₁ - (K₂/M₂)/(L₂/M₂ - ⋯))`.
  `DLMF.Heun.heunHypCFApprox` ([definition](DLMF/Heun/Basic.lean#L281)).

### §31.12 Confluent Forms of Heun’s Equation

<!-- retained entry 232 -->
- **Confluent, doubly confluent, biconfluent and triconfluent equations**,
  [31.12.1–4](https://dlmf.nist.gov/31.12.E1): `IsConfluentHeunSolOn`,
  `IsDoublyConfluentHeunSolOn`, `IsBiconfluentHeunSolOn`,
  `IsTriconfluentHeunSolOn` in [Basic](DLMF/Heun/Basic.lean#L347).
  These are solution predicates; no additional globally normalized
  confluent Heun function is selected there.

- **Irregular-singularity rank for confluent equations**, [DLMF 31.12.E1](https://dlmf.nist.gov/31.12.E1):
  `DLMF.Heun.HasIrregularRankAt` ([source](DLMF/Heun/Basic.lean#L380)), `DLMF.Heun.HasIrregularRankAtInfinity` ([source](DLMF/Heun/Basic.lean#L370)) encode finite/infinite irregular rank through coefficient growth after the reciprocal change of variable. They supplement the four confluent equation predicates, rather than choosing normalized confluent functions.

### §31.14 General Fuchsian Equation

<!-- retained entry 233 -->
- **Fuchsian equation, exponents and normal form**,
  [31.14.1–5](https://dlmf.nist.gov/31.14.E1): `fuchsianCoeffP`,
  `fuchsianCoeffR`, `IsFuchsianSolOn`, `fuchsianNormalQ`,
  `fuchsianNormalGamma`, `fuchsianNormalCoeff` in
  [Basic](DLMF/Heun/Basic.lean#L393). The singular points and coefficients
  are finite indexed families; α and β are constrained roots of the
  displayed quadratic, rather than globally chosen exponent definitions.

- **Liouvillean solutions and Kovacic algorithm**, [DLMF 31.14.ii](https://dlmf.nist.gov/31.14.ii):
  Liouvillean solutions are those expressible by finitely many algebraic operations, exponentials and quadratures in the indicated differential-algebraic setting. The prose describes Kovacic’s decision/construction algorithm for rational-coefficient equations. No general local Liouvillean predicate or Kovacic implementation was identified.

### §31.15 Stieltjes Polynomials

<!-- retained entry 234 -->
- **Stieltjes and Van Vleck polynomials**,
  [31.15.1](https://dlmf.nist.gov/31.15.E1): `fuchsianPi`,
  `fuchsianGammaPoly`, `IsStieltjesEquation`, `IsVanVleckStieltjes` in
  [Basic](DLMF/Heun/Basic.lean#L423), using the cleared polynomial
  differential equation and degree conditions.
  A separately selected monic Stieltjes polynomial `stieltjesPoly`,
  characterized by `IsStieltjesOfIndex` and prescribed numbers of roots
  between real singularities, is in
  [Basic](DLMF/Heun/Basic.lean#L453). Its intended existence and uniqueness
  for increasing real singularities and positive weights still rely on
  admitted `existsUnique_stieltjesOfIndex` in
  [Fuchsian](DLMF/Heun/Fuchsian.lean#L665); the definition falls back to zero
  if no unique polynomial exists. There is no separately selected
  Van Vleck polynomial function.

- **Stieltjes electrostatic density**, [DLMF 31.15.E4](https://dlmf.nist.gov/31.15.E4):
  DLMF 31.15.4: `G(ζ_1, …, ζ_n) = ∏_k ∏_ℓ (ζ_k - a_ℓ)^{γ_ℓ/2} ∏_{j > k} (ζ_k - ζ_j)`, principal
  powers.
  `DLMF.Heun.stieltjesG` ([definition](DLMF/Heun/Basic.lean#L443)).

- **Accessory charges and indexed root counts**, [DLMF 31.15.E7](https://dlmf.nist.gov/31.15.E7):
  `DLMF.Heun.rootsIn` ([source](DLMF/Heun/Basic.lean#L449)), `DLMF.Heun.IsStieltjesOfIndex` ([source](DLMF/Heun/Basic.lean#L453)) count polynomial roots in the real gaps and specify the monic polynomial with prescribed gap counts. The accessory qⱼ are finite inverse-distance sums in the electrostatic equations; no separate local selected Van Vleck/accessory-vector function is supplied. The root count uses polynomial roots, not a choice of their enumeration.

- **Stieltjes polynomial product**, [DLMF 31.15.E8](https://dlmf.nist.gov/31.15.E8):
  DLMF 31.15.8: the product `S_𝐦(z_1) ⋯ S_𝐦(z_{N-1})`.
  `DLMF.Heun.stieltjesProduct` ([definition](DLMF/Heun/Basic.lean#L479)).

- **Stieltjes ordered root chamber**, [DLMF 31.15.E10](https://dlmf.nist.gov/31.15.E10):
  DLMF 31.15.10: the box `Q = (a_1, a_2) × ⋯ × (a_{N-1}, a_N)` (here indexed from `0`).
  `DLMF.Heun.stieltjesBox` ([definition](DLMF/Heun/Basic.lean#L467)).

- **Stieltjes bilinear integral**, [DLMF 31.15.E11](https://dlmf.nist.gov/31.15.E11):
  DLMF 31.15.11: the inner product `(f, g)_ρ = ∫_Q f(z) conj(g(z)) ρ(z) dz`.
  `DLMF.Heun.stieltjesInner` ([definition](DLMF/Heun/Basic.lean#L484)).

- **DLMF 31.15.12: the weight**, [DLMF 31.15.E12](https://dlmf.nist.gov/31.15.E12):
  DLMF 31.15.12: the weight
  `ρ(z) = ∏_j ∏_k |z_j - a_k|^{γ_k - 1} · ∏_{j<k} (z_k - z_j)` on `Q`.
  `DLMF.Heun.stieltjesWeight` ([definition](DLMF/Heun/Basic.lean#L472)).

### §31.16 Mathematical Applications

- **Heun-product coordinates and Jacobi expansion coefficients**, [DLMF 31.16.E2](https://dlmf.nist.gov/31.16.E2):
  The implicit x,y coordinates, their three symmetric products, and coefficients Aⱼ with Pⱼ,Qⱼ,Rⱼ in 31.16.3–7 define an exact expansion scheme. No general local selected coordinate pair or A-sequence is constructed; the Heun and Jacobi polynomials in the representation are existing objects.

### §31.17 Physical Applications

- **Spin operators and elliptic sphere coordinates**, [DLMF 31.17.E1](https://dlmf.nist.gov/31.17.E1):
  J²,Hₛ, their common eigenfunction, the implicit elliptic coordinates z₁,z₂ and the parameter conversion in 31.17.2–5 are application definitions. No corresponding physical-operator or sphere-coordinate construction exists in the local Heun modules. §31.18’s matching/integration methods introduce no additional function families and are recorded descriptively.

## Chapter 32 — Painlevé transcendents

Expanded review: all 17 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§32.1–32.17 checked; matching headings are §§32.4(i)
and 32.7(i). The six equations in §32.2 are complementary entries.
Names below are in `DLMF.Painleve`.

### §32.2 Differential Equations

<!-- retained entry 235 -->
- **Painlevé I–VI and transformed Painlevé III′**,
  [32.2.1–6 and 32.2.9](https://dlmf.nist.gov/32.2.E1):
  `painleveIRhs`, `painleveIIRhs`, `painleveIIIRhs`, `painleveIVRhs`,
  `painleveVRhs`, `painleveVIRhs`, `painleveIIIPrimeRhs`, with predicates
  `IsPainleveIOn`, `IsPainleveIIOn`, `IsPainleveIIIOn`, `IsPainleveIVOn`,
  `IsPainleveVOn`, `IsPainleveVIOn`, `IsPainleveIIIPrimeOn`, in
  [Defs](DLMF/Painleve/Basic/Equations.lean#L87). The predicates retain the required
  nonvanishing denominators, rather than merely totalizing rational right
  sides. These specify families of solutions, not selected generic
  transcendents. The older `IsPIIOn c` in
  [Basic](DLMF/Painleve/Basic/BealsWong.lean#L52) uses the Beals–Wong parameter c=−α.

- **Second-order differential-equation solution predicate**, [DLMF 32.2.E7](https://dlmf.nist.gov/32.2.E7):
  DLMF 32.2.7: `w` solves the second-order equation `w'' = F(z, w, w')` on `U`. Both `w` and
  `w'` are required to be differentiable at every point of `U`, and the derivative of `w'` must
  be `F(z, w(z), w'(z))`. Intended for open `U` (the statements take `IsOpen U`).
  `DLMF.Painleve.IsODE2SolutionOn` ([definition](DLMF/Painleve/Basic/Equations.lean#L40)).

- **Painlevé property, movable singularities and equivalence**, [DLMF 32.2.E7](https://dlmf.nist.gov/32.2.E7):
  Movable singularities depend on initial/integration constants. The Painlevé property excludes movable branch points for every solution, allowing movable poles or isolated essential singularities in this definition. Möbius dependent-variable transformations with locally analytic coefficients and analytic changes of independent variable define the classification equivalence. No general local predicate for this property/equivalence is constructed; the six solution predicates alone do not formalize it.

- **Alternative forms and normalization changes**, [DLMF 32.2.E8](https://dlmf.nist.gov/32.2.E8):
  The PIII′ transformation is ζ=z², w=ζ^{−1/2}u and its equation is 32.2.9 (the retained entry’s former citation to 32.2.8 was only the preceding Möbius display). The sine form, quintic PIV oscillator, hyperbolic PV form and elliptic differential operator I in 32.2.10–14 are explicit supplied substitutions; no additional selected general solution or coordinate function is defined.

- **Symmetric systems and coalescence variables**, [DLMF 32.2.E15](https://dlmf.nist.gov/32.2.E15):
  The three-/four-component fⱼ systems with μ-sum and component-sum constraints give symmetric PIV/PV forms. The ε-dependent rescalings in 32.2.25–37 define the coalescence cascade substitutions. They are expressions in the transformation statements, not new local canonical solution families or limit selectors.

### §32.3 Graphics

- **Solutions specified for graphical examples**, [DLMF 32.3.i](https://dlmf.nist.gov/32.3.i):
  The plotted PI initial-data family wₖ, Airy-decaying PII family and parabolic-cylinder-decaying quintic-oscillator family are specified by exact boundary conditions before the plots. No local functions select these generic initial/asymptotic data families. The boundary-condition notions reappear in §32.11; plots and decimal initial thresholds are excluded: graphical/numerical.

### §32.4 Isomonodromy Problems

<!-- retained entry 236 -->
- **Lax pair and compatibility / zero curvature**,
  [32.4.1–3](https://dlmf.nist.gov/32.4.E1): there is no general local
  predicate selecting a fundamental matrix or defining isomonodromy.
  Explicit coefficient matrices `painleveILaxA`, `painleveILaxB`,
  `painleveIILaxA`, `painleveIILaxB`, `painleveIIILaxM`,
  `painleveIIILaxA`, `painleveIIILaxB`, with `laxSigma1`, `laxSigma2`,
  `laxSigma3`, are in [Defs](DLMF/Painleve/Basic/HamiltonianAndLax.lean#L85).
  The independent `laxA`, `laxB` in
  [LaxPair](DLMF/Painleve/LaxPair.lean#L41) use Beals–Wong's Painlevé-II
  spectral-variable and c=−α normalization. Matrix compatibility identities
  are theorems, not a construction of a global fundamental matrix or
  monodromy data.

- **Third-Painlevé auxiliary system and first integral**, [DLMF 32.4.E10](https://dlmf.nist.gov/32.4.E10):
  `DLMF.Painleve.painleveIIISystemRhs` ([source](DLMF/Painleve/Basic/HamiltonianAndLax.lean#L145)), `DLMF.Painleve.painleveIIILaxMDeriv` ([source](DLMF/Painleve/Basic/HamiltonianAndLax.lean#L139)) record the four-variable compatibility system and derivative of its matrix coefficient. The constant θ₀ of 32.4.16 and w=−u₀/(v₀v₁) are expressions in its reduction theorem, not separately chosen invariants or solutions.

### §32.5 Integral Equations

- **Airy integral-equation kernel**, [DLMF 32.5.E1](https://dlmf.nist.gov/32.5.E1):
  K(z,ζ) is characterized by the nonlinear integral equation with Airy kernel; its diagonal gives a PII solution with Airy boundary condition. No local K is defined by solving this equation; the existing Airy function and PII solution predicates do not constitute a selected integral-equation solution.

### §32.6 Hamiltonian Structure

- **Hamiltonian systems and sigma variables**, [DLMF 32.6.E1](https://dlmf.nist.gov/32.6.E1):
  `DLMF.Painleve.IsHamiltonianSystemOn` ([source](DLMF/Painleve/Basic/HamiltonianAndLax.lean#L40)) specifies q′=∂H/∂p,p′=−∂H/∂q. The five explicit Hamiltonians below are distinct normalization-dependent constructions. The σ combinations of 32.6.5, .13, .20, .28 and .36 and their inverse q,p formulas are local expressions in sigma-equation theorems; no globally selected σ transcendents are defined.

  [DLMF 32.6.E1](https://dlmf.nist.gov/32.6.E1):
  DLMF 32.6.1: `(q, p)` is a solution of the non-autonomous Hamiltonian system
  `q' = ∂H/∂p`, `p' = -∂H/∂q` on `U`; the partial derivatives are `deriv` of the sections of
  `H(q, p, z)` (in the theorems `H` is a polynomial, or rational with poles off `U`).
  `DLMF.Painleve.IsHamiltonianSystemOn` ([definition](DLMF/Painleve/Basic/HamiltonianAndLax.lean#L40)).

- **Painlevé-I Hamiltonian**, [DLMF 32.6.E2](https://dlmf.nist.gov/32.6.E2):
  DLMF 32.6.2: the Hamiltonian `H_I(q, p, z) = p²/2 - 2q³ - zq` of `PI`.
  `DLMF.Painleve.painleveHamiltonianI` ([definition](DLMF/Painleve/Basic/HamiltonianAndLax.lean#L52)).

- **Painlevé-II Hamiltonian**, [DLMF 32.6.E9](https://dlmf.nist.gov/32.6.E9):
  DLMF 32.6.9: the Hamiltonian `H_II(q, p, z) = p²/2 - (q² + z/2)p - (α + 1/2)q` of
  `PII`.
  `DLMF.Painleve.painleveHamiltonianII` ([definition](DLMF/Painleve/Basic/HamiltonianAndLax.lean#L56)).

- **Painlevé-III Hamiltonian**, [DLMF 32.6.E16](https://dlmf.nist.gov/32.6.E16):
  DLMF 32.6.16: the Hamiltonian of `PIII`,
  `z H_III = q²p² - (κ∞zq² + (2θ₀+1)q - κ₀z)p + κ∞(θ₀+θ∞)zq`, divided by `z` (junk value `0`
  at `z = 0`). Parameters in the order `κ₀ κ∞ θ₀ θ∞` (`κinf`, `θinf` in Lean).
  `DLMF.Painleve.painleveHamiltonianIII` ([definition](DLMF/Painleve/Basic/HamiltonianAndLax.lean#L62)).

- **Painlevé-III-prime Hamiltonian**, [DLMF 32.6.E24](https://dlmf.nist.gov/32.6.E24):
  DLMF 32.6.24: the Hamiltonian of `P'III`,
  `ζ H = q²p² - (η∞q² + θ₀q - η₀ζ)p + η∞(θ₀+θ∞)q/2`, divided by `ζ`. Parameters in the order
  `η₀ η∞ θ₀ θ∞`.
  `DLMF.Painleve.painleveHamiltonianIIIPrime` ([definition](DLMF/Painleve/Basic/HamiltonianAndLax.lean#L70)).

- **Degenerate Painlevé-III Hamiltonian with γ=0**, [DLMF 32.6.E32](https://dlmf.nist.gov/32.6.E32):
  DLMF 32.6.32: the Hamiltonian of `PIII` with `γ = 0`,
  `z H = q²p² + (θq - κ₀z)p - κ∞zq`, divided by `z`.
  `DLMF.Painleve.painleveHamiltonianIIIGammaZero` ([definition](DLMF/Painleve/Basic/HamiltonianAndLax.lean#L77)).

### §32.7 Bäcklund Transformations

<!-- retained entry 237 -->
- **Bäcklund transformations**, [§32.7(i)](https://dlmf.nist.gov/32.7.i):
  DLMF's prose describes transformations between Painlevé solutions and
  parameter values; there is no abstract local `BacklundTransformation`
  structure. The explicit Painlevé-II transformations `painleveIITPlus`,
  `painleveIITMinus` for [32.7.2](https://dlmf.nist.gov/32.7.E2) are in
  [Defs](DLMF/Painleve/Basic/Equations.lean#L203). The independently organized
  Beals–Wong operations `backlundReflect`, `backlundDown`, `backlundUp`
  in [Backlund](DLMF/Painleve/Backlund.lean#L35) act on the c=−α family;
  these require that parameter conversion when compared with DLMF.

- **Other Bäcklund maps and parameter transformations**, [DLMF 32.7.E3](https://dlmf.nist.gov/32.7.E3):
  Beyond the recorded PII maps, the special half-integer rescaling, PIII shifts, eight PIV/PV sign choices, PIII–PV relation and PVI Möbius/quadratic/quartic maps of 32.7.3–50 are explicit expressions in the transformation statements. No independent local generic map family, affine-Weyl action or root-sign selector is defined; denominator restrictions and paired square-root signs are part of their intended domains.

### §32.8 Rational Solutions

- **Rational solution predicate and independent Bäcklund construction**, [DLMF 32.8.i](https://dlmf.nist.gov/32.8.i):
  `DLMF.Painleve.IsRationalOn` ([source](DLMF/Painleve/Basic/Solutions.lean#L108)), `DLMF.Painleve.rationalFn` ([source](DLMF/Painleve/Rational.lean#L29)), `DLMF.Painleve.polynomialDomain` ([source](DLMF/Painleve/Rational.lean#L32)), `DLMF.Painleve.rationalStepDenom` ([source](DLMF/Painleve/Rational.lean#L54)), `DLMF.Painleve.rationalPIIPair` ([source](DLMF/Painleve/Rational.lean#L102)) specify polynomial-quotient solutions and construct an independent numerator/denominator recurrence from the zero seed. This recurrence retains common factors and uses Beals–Wong c=−α; it is not definitionally the monic Yablonskii–Vorob’ev quotient below. Polynomial exactness and equivalence require bridge results.

- **Rational Painlevé-II solutions**, [DLMF 32.8.E5](https://dlmf.nist.gov/32.8.E5):
  DLMF 32.8.5: the rational solution `w(z; n) = d/dz ln(Q_{n-1}(z)/Q_n(z))` of `PII` with
  `α = n`, written as the difference of logarithmic derivatives `Q_{n-1}'/Q_{n-1} - Q_n'/Q_n`
  (no logarithm branch is involved). For `n = 0` it is the seed `0`, and for negative `n` it is
  `w(z; n) = -w(z; -n)` (the symmetry `w ↦ -w`, `α ↦ -α`).
  `DLMF.Painleve.rationalPainleveII` ([definition](DLMF/Painleve/Basic/Solutions.lean#L67)).

- **Yablonskii–Vorob’ev polynomials**, [DLMF 32.8.E6](https://dlmf.nist.gov/32.8.E6):
  DLMF 32.8.6: the Yablonskii–Vorob'ev polynomials, `Q₀ = 1`, `Q₁ = z` and
  `Q_{n+1} Q_{n-1} = z Q_n² + 4 (Q_n')² - 4 Q_n Q_n''`. The recurrence is implemented with
  polynomial division by `Q_{n-1}`; that the division is exact is part of 32.8.6.
  `DLMF.Painleve.yablonskiiVorobievQ` ([definition](DLMF/Painleve/Basic/Solutions.lean#L55)).

- **Generating polynomials versus Wronskian tau normalization**, [DLMF 32.8.E8](https://dlmf.nist.gov/32.8.E8):
  The pₘ of `DLMF.Painleve.yablonskiiVorobievP` ([source](DLMF/Painleve/Basic/Solutions.lean#L84)) only have natural indices; DLMF additionally defines pₘ=0 for m<0. `DLMF.Painleve.yablonskiiVorobievTau` ([source](DLMF/Painleve/Basic/Solutions.lean#L92)) is the Wronskian determinant, distinct from the monic Qₙ normalization even when their logarithmic derivatives represent the same solution. The rational PIII–PVI examples in §§32.8(iii)–(vi) are polynomial quotients in solution theorems, not selected general P/Q hierarchies.

  [DLMF 32.8.E8](https://dlmf.nist.gov/32.8.E8):
  DLMF 32.8.8: the polynomials `p_m(z)` with `∑ p_m(z) λ^m = exp(zλ - (4/3)λ³)`,
  `p_m(z) = ∑_{3j ≤ m} (-4/3)^j z^{m-3j} / (j! (m-3j)!)`. (DLMF also sets `p_m = 0` for
  `m < 0`; only `m ≥ 0` occurs here.)
  `DLMF.Painleve.yablonskiiVorobievP` ([definition](DLMF/Painleve/Basic/Solutions.lean#L84)).

  [DLMF 32.8.E10](https://dlmf.nist.gov/32.8.E10):
  DLMF 32.8.10: the `n × n` Wronskian `τ_n = 𝒲{p₁, p₃, …, p_{2n-1}}`, the determinant of
  `(p_{2j+1}^{(i)})_{0 ≤ i, j < n}`; `τ₀ = 1`.
  `DLMF.Painleve.yablonskiiVorobievTau` ([definition](DLMF/Painleve/Basic/Solutions.lean#L92)).

### §32.9 Other Elementary Solutions

- **Algebraic and elementary solution families**, [DLMF 32.9.E1](https://dlmf.nist.gov/32.9.E1):
  `DLMF.Painleve.IsAlgebraicOn` ([source](DLMF/Painleve/Basic/Solutions.lean#L113)) requires a nonzero bivariate polynomial relation on the supplied domain. The displayed fractional-power, logarithmic, exponential and quadrature solutions are expressions using existing functions. No general local family selects the algebraic PIII/PV polynomials or arbitrary first-integral branches; parameter-dependent elementary representations do not define generic Painlevé transcendents.

### §32.10 Special Function Solutions

- **Airy seed, derivative and iterated half-integer hierarchy**, [DLMF 32.10.E5](https://dlmf.nist.gov/32.10.E5):
  `DLMF.Painleve.airySeed` ([source](DLMF/Painleve/Airy.lean#L38)), `DLMF.Painleve.airySeedDeriv` ([source](DLMF/Painleve/Airy.lean#L41)), `DLMF.Painleve.airyPII` ([source](DLMF/Painleve/Airy.lean#L62)), `DLMF.Painleve.airyPIIJet` ([source](DLMF/Painleve/Airy.lean#L96)), `DLMF.Painleve.airyPIIHierarchy` ([source](DLMF/Painleve/Airy.lean#L187)) give actual scaled Airy combinations and a rational Bäcklund hierarchy. They use a cube-root scale k³=−1/2 and the Beals–Wong convention c=−α; thus `airyPII` at c=1/2 is DLMF α=−1/2. These are explicit constructions rather than choices from admitted existence principles. `DLMF.Painleve.TauEquationsAt` ([source](DLMF/Painleve/Tau.lean#L27)), `DLMF.Painleve.tauQuotientDeriv` ([source](DLMF/Painleve/Tau.lean#L33)) are a separate bilinear quotient representation in that convention, not the Wronskian determinant `wronskianTau`.

  [DLMF 32.10.E9](https://dlmf.nist.gov/32.10.E9):
  DLMF 32.10.9: the `n × n` Wronskian `τ_n(z) = 𝒲{φ, φ', …, φ⁽ⁿ⁻¹⁾}(z)`, the determinant of
  `(φ^{(i+j)}(z))_{0 ≤ i, j < n}`; `τ₀ = 1`.
  `DLMF.Painleve.wronskianTau` ([definition](DLMF/Painleve/Basic/Solutions.lean#L100)).

- **Bessel, cylinder, Whittaker and hypergeometric Riccati seeds**, [DLMF 32.10.E14](https://dlmf.nist.gov/32.10.E14):
  The φ combinations in 32.10.14, .19, .27 and .31, their logarithmic derivatives and the Hermite/erfc special cases are explicit expressions in existing function families. No additional general local named φ construction selects all of these branches. Their free constants, scaled arguments and denominator-zero exclusions remain essential.

- **Picard inverse elliptic integral and invariants**, [DLMF 32.10.E32](https://dlmf.nist.gov/32.10.E32):
  `DLMF.Painleve.picardG₂` ([source](DLMF/Painleve/Basic/Solutions.lean#L247)), `DLMF.Painleve.picardG₃` ([source](DLMF/Painleve/Basic/Solutions.lean#L252)), `DLMF.Painleve.picardLambda` ([source](DLMF/Painleve/Basic/Solutions.lean#L256)) construct Λ in Weierstrass form with an explicitly supplied half-period ω₀ satisfying the prescribed root value. The definition does not choose that half-period or the two period solutions φ₁,φ₂. The normalization Λ=4℘(u+ω₀)+(1+z)/3 preserves Λ(0,z)=0 under the half-period hypothesis; z=0,1 are degenerate cases.

### §32.11 Asymptotic Approximations for Real Variables

- **Real solution equations and asymptotic phase data**, [DLMF 32.11.E1](https://dlmf.nist.gov/32.11.E1):
  `DLMF.Painleve.IsRealODE2SolutionOn` ([source](DLMF/Painleve/Basic/Solutions.lean#L121)), `DLMF.Painleve.realPainleveIRhs` ([source](DLMF/Painleve/Basic/Solutions.lean#L129)), `DLMF.Painleve.realPainleveIIRhs` ([source](DLMF/Painleve/Basic/Solutions.lean#L132)), `DLMF.Painleve.modifiedPainleveIIRhs` ([source](DLMF/Painleve/Basic/Solutions.lean#L136)), `DLMF.Painleve.realPainleveIIIRhs` ([source](DLMF/Painleve/Basic/Solutions.lean#L140)), `DLMF.Painleve.realPainleveIVRhs` ([source](DLMF/Painleve/Basic/Solutions.lean#L144)) are actual real equation/data constructions. The phase functions φ,ψ, connection quantities d,θ₀,σ,ρ,s,B,μ and critical h*=1/(√πΓ(ν+1)) are explicit formulas in the asymptotic statements. No local general selector supplies the Airy-decaying wₖ, modified PII connection solution or PIV wₕ families. Their exact asymptotic characterizations are mathematical; printed decimal thresholds are excluded: numerical.

  [DLMF 32.11.E12](https://dlmf.nist.gov/32.11.E12):
  The right-hand side `-2w³ + xw` of the modified `PII` equation, DLMF 32.11.12.
  `DLMF.Painleve.modifiedPainleveIIRhs` ([definition](DLMF/Painleve/Basic/Solutions.lean#L136)).

### §32.13 Reductions of Partial Differential Equations

- **Integrable PDE predicates and similarity coordinates**, [DLMF 32.13.E1](https://dlmf.nist.gov/32.13.E1):
  `DLMF.Painleve.IsMKdVOn` ([source](DLMF/Painleve/Basic/Solutions.lean#L155)), `DLMF.Painleve.IsKdVOn` ([source](DLMF/Painleve/Basic/Solutions.lean#L169)), `DLMF.Painleve.IsSineGordonOn` ([source](DLMF/Painleve/Basic/Solutions.lean#L181)), `DLMF.Painleve.IsBoussinesqOn` ([source](DLMF/Painleve/Basic/Solutions.lean#L192)) encode the PDEs with derivative witnesses. The scaling variables z=x(3t)^{−1/3}, z=xt, z=x−ct and shifted KdV coordinate are explicit substitutions in reduction theorems; no new selected PDE solutions are defined.

  [DLMF 32.13.E1](https://dlmf.nist.gov/32.13.E1):
  DLMF 32.13.1: the modified Korteweg–de Vries equation `v_t - 6v²v_x + v_xxx = 0` on
  `U ⊆ ℂ × ℂ`.
  `DLMF.Painleve.IsMKdVOn` ([definition](DLMF/Painleve/Basic/Solutions.lean#L155)).

  [DLMF 32.13.E3](https://dlmf.nist.gov/32.13.E3):
  DLMF 32.13.3: the Korteweg–de Vries equation `u_t + 6uu_x + u_xxx = 0` on `U`.
  `DLMF.Painleve.IsKdVOn` ([definition](DLMF/Painleve/Basic/Solutions.lean#L169)).

  [DLMF 32.13.E6](https://dlmf.nist.gov/32.13.E6):
  DLMF 32.13.6: the sine-Gordon equation `u_xt = sin u` on `U`; the mixed derivative is the
  `t`-derivative of `u_x`.
  `DLMF.Painleve.IsSineGordonOn` ([definition](DLMF/Painleve/Basic/Solutions.lean#L181)).

  [DLMF 32.13.E8](https://dlmf.nist.gov/32.13.E8):
  DLMF 32.13.8: the Boussinesq equation `u_tt = u_xx - 6(u²)_xx + u_xxxx` on `U`.
  `DLMF.Painleve.IsBoussinesqOn` ([definition](DLMF/Painleve/Basic/Solutions.lean#L192)).

### §32.14 Combinatorics

- **Longest increasing subsequence length**, [DLMF 32.14](https://dlmf.nist.gov/32.14):
  §32.14: the length `ℓ_N(π)` of the longest increasing subsequence of a permutation `π`
  of `{0, …, N-1}`: the largest cardinality of a set of positions on which `π` is strictly
  increasing.
  `DLMF.Painleve.longestIncreasingLength` ([definition](DLMF/Painleve/Basic/Solutions.lean#L209)).

- **Tracy–Widom distribution function**, [DLMF 32.14.E2](https://dlmf.nist.gov/32.14.E2):
  DLMF 32.14.2: `F(s) = exp(-∫_s^∞ (x - s) w(x)² dx)` for a real function `w` (in 32.14
  the Hastings–McLeod solution of `PII` with `α = 0`). The integral is a Bochner integral over
  `(s, ∞)`, totalized to `0` when not integrable.
  `DLMF.Painleve.tracyWidomF` ([definition](DLMF/Painleve/Basic/Solutions.lean#L218)).

- **Tracy–Widom expression versus a selected distribution**, [DLMF 32.14.E2](https://dlmf.nist.gov/32.14.E2):
  The existing `tracyWidomF w` takes an arbitrary real w; it becomes the stated distribution only with the Hastings–McLeod boundary conditions and integrability. No local function selects that particular w or bundles a probability distribution from this expression. `longestIncreasingLength` uses zero-based permutations, preserving the source statistic after relabelling.

### §32.15 Orthogonal Polynomials

- **Freud weight, moments and Hankel recurrence data**, [DLMF 32.15.E1](https://dlmf.nist.gov/32.15.E1):
  `DLMF.Painleve.freudMoment` ([source](DLMF/Painleve/Basic/Solutions.lean#L227)), `DLMF.Painleve.freudHankel` ([source](DLMF/Painleve/Basic/Solutions.lean#L232)), `DLMF.Painleve.freudRecurrenceSq` ([source](DLMF/Painleve/Basic/Solutions.lean#L237)) give the exact quartic-exponential moments, Hankel determinants and squared recurrence coefficient. No local orthonormal polynomial family pₙ or signed aₙ is independently selected from those moments. The determinant ratio uses totalized division; its positive-measure characterization requires the relevant nonzero determinant results. §§32.12,32.16–17 add references/methods rather than new explicit mathematical definitions.

  [DLMF 32.15.E1](https://dlmf.nist.gov/32.15.E1):
  The moments `μ_k(z) = ∫_ℝ ξ^k exp(-ξ⁴/4 - zξ²) dξ` of the weight of DLMF 32.15.1.
  `DLMF.Painleve.freudMoment` ([definition](DLMF/Painleve/Basic/Solutions.lean#L227)).

  [DLMF 32.15.E2](https://dlmf.nist.gov/32.15.E2):
  DLMF 32.15.2: the squared recurrence coefficient `u_n(z) = a_n(z)²` of the orthonormal
  polynomials of DLMF 32.15.1, in the classical Hankel-determinant form
  `a_n² = D_{n-1}D_{n+1}/D_n²` (`n ≥ 1`; `u_0 = 0`, the convention `a_0 = 0` that makes 32.15.2
  also hold for `n = 0` with `p_{-1} = 0`).
  `DLMF.Painleve.freudRecurrenceSq` ([definition](DLMF/Painleve/Basic/Solutions.lean#L237)).

## Chapter 33 — Coulomb functions

Expanded review: all 26 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§33.1–33.26 checked; matching headings are §§33.2,
33.14 and 33.22(ii). The last is an application-specific variable dictionary,
recorded here because its heading matches, without acquiring physical models.

Names in this subsection are in `DLMF.Coulomb`.

### §33.1 Special Notation

- **Alternative Coulomb normalizations**, [DLMF 33.1](https://dlmf.nist.gov/33.1):
  Curtis’s Pℓ,Qℓ are factorial/A-scaled f,h; Greene’s f⁽⁰⁾,f,g correspond to DLMF f,s,c. These are notation/normalization dictionaries, without separate local wrapper functions. They must not be confused with the large-ρ amplitudes f,g introduced later in §33.11.

### §33.2 Definitions and Basic Properties

<!-- retained entry 238 -->
- **Coulomb equation and outer turning point ρₜₚ**,
  [33.2.1–2](https://dlmf.nist.gov/33.2.E1):
  `DLMF.Coulomb.turningPoint` in [Basic](DLMF/Coulomb/Basic/Functions.lean#L101).
  The differential equation is expressed in solution theorems rather than a
  separate named Coulomb-ODE predicate.

<!-- retained entry 239 -->
- **Regular Coulomb Fℓ and normalizing Cℓ**,
  [33.2.3–6](https://dlmf.nist.gov/33.2.E3):
  `DLMF.Confluent.coulombF`, `coulombC`, and the unnormalized complex
  `coulombWave`, with `coulombWaveDeriv`, in
  [Basic](DLMF/Coulomb/Basic/Functions.lean#L42). The real function is the real part
  of C times the native Kummer-M formula. The Whittaker form is a bridge,
  not a second defined F. A genuinely wider complex-parameter definition
  `DLMF.Coulomb.coulombWaveComplex` is in
  [Defs](DLMF/Coulomb/Basic/AuxiliaryData.lean#L144); this remains unnormalized and uses a
  principal power for complex ℓ. It agrees with `coulombWave` at natural ℓ;
  comparison with F also needs the real normalization Cℓ.

<!-- retained entry 240 -->
- **Outgoing/incoming Hℓ± and irregular Gℓ**,
  [33.2.7–8 and 33.2.11](https://dlmf.nist.gov/33.2.E7):
  `DLMF.Confluent.coulombHPlus`, `coulombHMinus`, `coulombG` in
  [Basic](DLMF/Coulomb/Basic/Functions.lean#L75), actual Kummer-U formulas followed
  by real part for G. `coulombAPlus` exposes the coefficient of the
  unscaled U form. Whittaker-W representations are bridges.

<!-- retained entry 241 -->
- **Coulomb phase θℓ and phase shift σℓ**,
  [33.2.9–10](https://dlmf.nist.gov/33.2.E9):
  `DLMF.Confluent.coulombTheta`, `coulombSigma` in
  [Basic](DLMF/Coulomb/Basic/Functions.lean#L67) use the principal `Complex.arg` of
  Gamma. The separate `DLMF.Coulomb.phaseShift` in
  [Defs](DLMF/Coulomb/Basic/AuxiliaryData.lean#L58) is an arctangent series and finite
  sum, implementing DLMF's continuous phase with value zero at η=0.
  These are not equal as real-valued phase functions globally; their
  exponentials are compared by `exp_I_phaseShift` in
  [RhoEtaProperties](DLMF/Coulomb/RhoEtaProperties.lean#L511).

### §33.3 Graphics

- **Coulomb modulus Mℓ**, [DLMF 33.3.E1](https://dlmf.nist.gov/33.3.E1):
  Mℓ=√(Fℓ²+Gℓ²)=|Hℓ±| is a mathematical definition in the graphics section. No separately named local Coulomb-modulus object is constructed; it is an expression in the existing F,G,H functions. The plots and decimal turning-point evaluations are excluded: graphical/numerical.

### §33.4 Recurrence Relations and Derivatives

- **Coulomb recurrence coefficients R, S and T**, [DLMF 33.4.E1](https://dlmf.nist.gov/33.4.E1):
  The recurrence coefficient `R_ℓ = (1 + η²/ℓ²)^{1/2}` (DLMF 33.4.1), for `ℓ ≥ 1`.
  `DLMF.Coulomb.recurrenceR` ([definition](DLMF/Coulomb/Basic/AuxiliaryData.lean#L46)).

  [DLMF 33.4.E1](https://dlmf.nist.gov/33.4.E1):
  The recurrence coefficient `S_ℓ = ℓ/ρ + η/ℓ` (DLMF 33.4.1), for `ℓ ≥ 1`.
  `DLMF.Coulomb.recurrenceS` ([definition](DLMF/Coulomb/Basic/AuxiliaryData.lean#L50)).

  [DLMF 33.4.E1](https://dlmf.nist.gov/33.4.E1):
  The recurrence coefficient `T_ℓ = S_ℓ + S_{ℓ+1}` (DLMF 33.4.1), for `ℓ ≥ 1`.
  `DLMF.Coulomb.recurrenceT` ([definition](DLMF/Coulomb/Basic/AuxiliaryData.lean#L54)).

### §33.6 Power-Series Expansions in ρ

- **Shifted regular-series coefficient recurrence**, [DLMF 33.6.E3](https://dlmf.nist.gov/33.6.E3):
  `DLMF.Coulomb.powerSeriesCoeffAux` ([source](DLMF/Coulomb/Basic/AuxiliaryData.lean#L67)) is the shifted recurrence underlying the indexed `powerSeriesCoeff`; coefficients below ℓ+1 are zero in the latter. The hypergeometric formula in 33.6.4 is a bridge, not a second native coefficient sequence. The logarithmic H± expansion is a representation of the Kummer-U construction, including exceptional-parameter limits.

  [DLMF 33.6.E3](https://dlmf.nist.gov/33.6.E3):
  The coefficient `A_k^ℓ(η)` of the power series `F_ℓ = C_ℓ ∑_{k ≥ ℓ+1} A_k^ℓ ρ^k`
  (DLMF 33.6.1, 33.6.3), extended by `0` for `k ≤ ℓ`.
  `DLMF.Coulomb.powerSeriesCoeff` ([definition](DLMF/Coulomb/Basic/AuxiliaryData.lean#L75)).

### §33.7 Integral Representations

- **Coulomb integral representatives**, [DLMF 33.7.E1](https://dlmf.nist.gov/33.7.E1):
  The finite Euler integral for F and three half-line/contour integrals for H± in 33.7.1–4 are representation theorems for the existing functions, not separately named exact-integral constructions. They retain principal powers/arctangent and the specified contour; an arbitrary straight principal-branch integral is not interchangeable with the contour expression.

### §33.8 Continued Fractions

- **Logarithmic-derivative parameters and scaled recurrence solutions**, [DLMF 33.8.E3](https://dlmf.nist.gov/33.8.E3):
  a,b,c and u,p,q are explicit parameters/logarithmic derivatives in the continued-fraction formulas. `DLMF.Coulomb.q2a_u` ([source](DLMF/Coulomb/RhoEtaRepresentations.lean#L618)), `DLMF.Coulomb.q2a_w` ([source](DLMF/Coulomb/RhoEtaRepresentations.lean#L665)) separately construct the normalized Kummer factor and a product-scaled backward solution used in this representation. They are normalization helpers for existing F, not further Coulomb wave functions. No general function selects the ambiguous reconstruction sign from finite numerical convergence.

### §33.9 Expansions in Series of Bessel Functions

- **Coulomb–Bessel expansion coefficients a**, [DLMF 33.9.E2](https://dlmf.nist.gov/33.9.E2):
  The coefficients `a_k` of the spherical Bessel series DLMF 33.9.1:
  `a_0 = (2ℓ+1)!! C_ℓ(η)`, `a_{-1} = 0` and the recurrence DLMF 33.9.2,
  `k(k+2ℓ+1)/(2k+2ℓ+1) a_k - 2η a_{k-1} + (k-2)(k+2ℓ-1)/(2k+2ℓ-3) a_{k-2} = 0`.
  `DLMF.Coulomb.besselSeriesCoeffA` ([definition](DLMF/Coulomb/Basic/AuxiliaryData.lean#L81)).

- **Bessel-series coefficient indexing and λℓ**, [DLMF 33.9.E5](https://dlmf.nist.gov/33.9.E5):
  The auxiliary `DLMF.Coulomb.besselSeriesCoeffBAux` ([source](DLMF/Coulomb/Basic/AuxiliaryData.lean#L92)) shifts the bₖ recurrence used by `besselSeriesCoeffB`; `besselSeriesCoeffA` uses the spherical-series initial data. The λℓ of 33.9.7 is specified asymptotically, not by a convergent sum, and no independently selected local λℓ function was found.

  [DLMF 33.9.E5](https://dlmf.nist.gov/33.9.E5):
  The coefficient `b_k` of DLMF 33.9.3–33.9.5 (`η ≠ 0`), extended by `0` for `k < 2ℓ`.
  `DLMF.Coulomb.besselSeriesCoeffB` ([definition](DLMF/Coulomb/Basic/AuxiliaryData.lean#L102)).

### §33.11 Asymptotic Expansions for Large ρ

- **Large-ρ complex Coulomb amplitude**, [DLMF 33.11.E2](https://dlmf.nist.gov/33.11.E2):
  The amplitude `f(η,ρ) = G_ℓ cos θ_ℓ + F_ℓ sin θ_ℓ` of DLMF 33.11.2 (the unique `f` with
  33.11.2 together with `largeRhoG`).
  `DLMF.Coulomb.largeRhoF` ([definition](DLMF/Coulomb/Basic/AuxiliaryData.lean#L107)).

- **Large-ρ Coulomb amplitude and phase components**, [DLMF 33.11.E3](https://dlmf.nist.gov/33.11.E3):
  The amplitude `f̂(η,ρ) = G_ℓ' cos θ_ℓ + F_ℓ' sin θ_ℓ` of DLMF 33.11.3 (derivatives in
  `ρ`).
  `DLMF.Coulomb.largeRhoFHat` ([definition](DLMF/Coulomb/Basic/AuxiliaryData.lean#L118)).

  [DLMF 33.11.E3](https://dlmf.nist.gov/33.11.E3):
  The amplitude `ĝ(η,ρ) = F_ℓ' cos θ_ℓ - G_ℓ' sin θ_ℓ` of DLMF 33.11.3.
  `DLMF.Coulomb.largeRhoGHat` ([definition](DLMF/Coulomb/Basic/AuxiliaryData.lean#L125)).

- **Large-ρ Coulomb asymptotic terms**, [DLMF 33.11.E8](https://dlmf.nist.gov/33.11.E8):
  The terms `(f_k, g_k, f̂_k, ĝ_k)` of DLMF 33.11.5–33.11.6: `f_0 = 1`, `g_0 = 0`,
  `f̂_0 = 0`, `ĝ_0 = 1 - η/ρ` and the recurrence DLMF 33.11.8 with `λ_k`, `μ_k` of 33.11.9.
  `DLMF.Coulomb.largeRhoTerm` ([definition](DLMF/Coulomb/Basic/AuxiliaryData.lean#L131)).

- **Large-radius recurrence parameters**, [DLMF 33.11.E9](https://dlmf.nist.gov/33.11.E9):
  The λₖ,μₖ of 33.11.9 are local expressions inside `DLMF.Coulomb.largeRhoTerm` ([source](DLMF/Coulomb/Basic/AuxiliaryData.lean#L131)). The four actual amplitudes f,g,f̂,ĝ are obtained from the exact Coulomb functions and their derivatives; the recursively generated terms describe their expansions and are not definitions by summing a divergent asymptotic series.

### §33.12 Asymptotic Expansions for Large η

- **Coulomb transition coordinates x and μ**, [DLMF 33.12.E1](https://dlmf.nist.gov/33.12.E1):
  The transition-region variable `x = (2η - ρ)/(2η)^{1/3}` of DLMF 33.12.1 (`η > 0`).
  `DLMF.Coulomb.transitionX` ([definition](DLMF/Coulomb/Basic/AuxiliaryData.lean#L150)).

  [DLMF 33.12.E1](https://dlmf.nist.gov/33.12.E1):
  The large parameter `μ = (2η)^{2/3}` of DLMF 33.12.1 (`η > 0`).
  `DLMF.Coulomb.transitionMu` ([definition](DLMF/Coulomb/Basic/AuxiliaryData.lean#L154)).

- **Displayed transition coefficients versus the full sequence**, [DLMF 33.12.E4](https://dlmf.nist.gov/33.12.E4):
  The actual `transitionA` and `transitionB` definitions encode only A₁,A₂,A₃ and B₁,B₂,B₃ and return zero at every other index. They cover the explicit displayed polynomials, not the complete sequences in 33.12.2–3. Those full sequences remain a definition gap. The turning-point variables x,μ and ω=(2η/3)^{1/3}, and the uniform coordinate z=ρ/(2η), retain η>0; ω,z are expressions without extra named wrappers.

  [DLMF 33.12.E4](https://dlmf.nist.gov/33.12.E4):
  The polynomials `A_1, A_2, A_3` of DLMF 33.12.4 (`A_k = 0` for other `k`).
  `DLMF.Coulomb.transitionA` ([definition](DLMF/Coulomb/Basic/AuxiliaryData.lean#L158)).

  [DLMF 33.12.E5](https://dlmf.nist.gov/33.12.E5):
  The polynomials `B_1, B_2, B_3` of DLMF 33.12.5 (`B_k = 0` for other `k`).
  `DLMF.Coulomb.transitionB` ([definition](DLMF/Coulomb/Basic/AuxiliaryData.lean#L167)).

### §33.13 Complex Variable and Parameters

- **Complex-order normalization gap**, [DLMF 33.13.E1](https://dlmf.nist.gov/33.13.E1):
  The independent `coulombWaveComplex` gives the unnormalized regular Kummer expression for complex ℓ,η,ρ. No matching globally consistent complex normalization Cℓ, continued phase σℓ, complex Rℓ and normalized F/G/H family satisfying 33.13.1–2 is selected. The existing real η/nonnegative-integer ℓ formulas do not supply all these continuations by themselves.

### §33.14 Definitions and Basic Properties

<!-- retained entry 242 -->
- **Energy/radius variables ε,r and κ, and turning point rₜₚ**,
  [33.14.1–3 and 33.14.6](https://dlmf.nist.gov/33.14.E2):
  `coulombKappa`, `turningPointR` in
  [Energy/Defs](DLMF/Coulomb/Energy/Basic.lean#L61).
  The change r=−ηρ, ε=1/η² is used as an expression, without separate
  conversion objects. κ uses the upper imaginary sign when ε>0 and the
  sign of r when ε<0; ε=0 has a fallback value.

<!-- retained entry 243 -->
- **Regular f(ε,ℓ;r)**, [33.14.4–5](https://dlmf.nist.gov/33.14.E4):
  `coulombfKummer`, `coulombf` in
  [Energy/Defs](DLMF/Coulomb/Energy/Basic.lean#L70). For nonzero ε the
  definition takes the real part of the Kummer formula; ε=0 is filled by
  a regularized ₀F₁ expression. The Whittaker and Bessel forms are
  representations of this function, not additional selected functions.

<!-- retained entry 244 -->
- **Irregular h and piecewise S(ε,r)**,
  [33.14.7–8](https://dlmf.nist.gov/33.14.E7): `coulombSFactor`,
  `coulombhKappa`, `coulombhFormula`, `coulombh` in
  [Energy/Defs](DLMF/Coulomb/Energy/Basic.lean#L86).
  The first two formula objects expose the Whittaker/Kummer construction;
  the final real function fills ε=0 and Gamma-pole parameters by
  `limUnder` in ε. Existence and the intended values of such limits need
  separate results; merely having the totalized limit object is not proof
  of analytic continuation. r=0 remains outside the intended domain.

<!-- retained entry 245 -->
- **Energy-normalized s,c and factors A,B**,
  [33.14.9–12](https://dlmf.nist.gov/33.14.E9): `coulombAProd`,
  `coulombBFactor`, `coulombs`, `coulombc` in
  [Energy/Defs](DLMF/Coulomb/Energy/Basic.lean#L123).
  A is the finite product; its Gamma ratio is a theorem bridge. The
  functions s,c are complex and retain the principal powers when B<0,
  as required by DLMF; c at B=0 is totalized.

<!-- retained entry 246 -->
- **Hydrogenic radial φₙ,ℓ**, [33.14.14](https://dlmf.nist.gov/33.14.E14):
  `hydrogenRadial` in [Energy/Defs](DLMF/Coulomb/Energy/Basic.lean#L152),
  defined from f at ε=−1/n² and real normalization factors. The Laguerre
  expression is an equivalence theorem, for the DLMF range n≥ℓ+1.

### §33.16 Connection Formulas

- **Energy conversion parameters and Whittaker auxiliaries**, [DLMF 33.16.E3](https://dlmf.nist.gov/33.16.E3):
  τ=√ε for ε>0 and ν=1/√(−ε) for ε<0 are substitution expressions. The separately defined ζℓ,ξℓ,K are `coulombZeta`, `coulombXi`, `coulombKNorm` below, with their positive-ν and branch conventions. These exact Whittaker formulas coexist with the f/h functions; the connection identities are bridges, not alternate definitions of f/h.

  [DLMF 33.16.E9](https://dlmf.nist.gov/33.16.E9):
  `ζ_ℓ(ν,r) = W_{ν,ℓ+1/2}(2r/ν)` (DLMF 33.16.9), written as
  `e^{-z/2} z^{ℓ+1} U(ℓ+1-ν, 2ℓ+2, z)` with `z = 2r/ν` (principal branch).
  `DLMF.Coulomb.coulombZeta` ([definition](DLMF/Coulomb/Energy/Basic.lean#L161)).

  [DLMF 33.16.E9](https://dlmf.nist.gov/33.16.E9):
  `ξ_ℓ(ν,r) = Re(e^{iπν} W_{-ν,ℓ+1/2}(e^{iπ} 2r/ν))` (DLMF 33.16.9). The argument
  `e^{iπ} 2r/ν` is the complex number `-(2r/ν)`; for `2r/ν > 0` it lies on the negative real axis,
  where the principal branch takes `ph = π` (the value from the upper half-plane), as DLMF's
  `e^{iπ}` prescribes.
  `DLMF.Coulomb.coulombXi` ([definition](DLMF/Coulomb/Energy/Basic.lean#L168)).

  [DLMF 33.16.E16](https://dlmf.nist.gov/33.16.E16):
  `K(ν,ℓ) = (ν² Γ(ν+ℓ+1) Γ(ν-ℓ))^{-1/2}` (DLMF 33.16.16), with the real power; it is the
  intended value when `Γ(ν-ℓ) > 0`, that is when `A(-1/ν², ℓ) > 0`.
  `DLMF.Coulomb.coulombKNorm` ([definition](DLMF/Coulomb/Energy/Basic.lean#L178)).

### §33.19 Power-Series Expansions in r

- **Zero-energy Coulomb normalization α**, [DLMF 33.19.E2](https://dlmf.nist.gov/33.19.E2):
  The coefficients `α_k` of the power series 33.19.1 of `f(ε,ℓ;r)` (DLMF 33.19.2):
  `α₀ = 2^{ℓ+1}/(2ℓ+1)!`, `α₁ = -α₀/(ℓ+1)` and
  `k(k+2ℓ+1) α_k + 2α_{k-1} + εα_{k-2} = 0` for `k ≥ 2`.
  `DLMF.Coulomb.coulombAlpha` ([definition](DLMF/Coulomb/Energy/Basic.lean#L184)).

- **Zero-energy Coulomb coefficients γ**, [DLMF 33.19.E4](https://dlmf.nist.gov/33.19.E4):
  The coefficients `γ_k` of DLMF 33.19.3–33.19.4: `γ₀ = γ₁ = 1` and
  `γ_k - γ_{k-1} + (1/4)(k-1)(k-2ℓ-2) ε γ_{k-2} = 0` for `k ≥ 2`.
  `DLMF.Coulomb.coulombGammaCoeff` ([definition](DLMF/Coulomb/Energy/Basic.lean#L194)).

- **Zero-energy Coulomb coefficients δ**, [DLMF 33.19.E5](https://dlmf.nist.gov/33.19.E5):
  The coefficients `δ_k` of DLMF 33.19.5–33.19.6:
  `δ₀ = (β_{2ℓ+1} - 2(ψ(2ℓ+2) + ψ(1)) A(ε,ℓ)) α₀`, `δ₁ = (β_{2ℓ+2} - 2(ψ(2ℓ+3) + ψ(2)) A(ε,ℓ)) α₁`
  and `k(k+2ℓ+1) δ_k + 2δ_{k-1} + εδ_{k-2} + 2(2k+2ℓ+1) A(ε,ℓ) α_k = 0` for `k ≥ 2`.
  `DLMF.Coulomb.coulombDeltaCoeff` ([definition](DLMF/Coulomb/Energy/Basic.lean#L213)).

- **Zero-energy Coulomb coefficients β**, [DLMF 33.19.E7](https://dlmf.nist.gov/33.19.E7):
  The coefficients `β_k` of DLMF 33.19.7: `β₀ = β₁ = 0` and
  `β_k - β_{k-1} + (1/4)(k-1)(k-2ℓ-2) ε β_{k-2} + (1/2)(k-1) ε γ_{k-2} = 0` for `k ≥ 2`.
  `DLMF.Coulomb.coulombBetaCoeff` ([definition](DLMF/Coulomb/Energy/Basic.lean#L203)).

### §33.20 Expansions for Small | ϵ |

- **Energy-series coefficient functions Fk and Hk**, [DLMF 33.20.E4](https://dlmf.nist.gov/33.20.E4):
  The finite Bessel sums Fk,Hk in 33.20.4–5 and .8–9 use the full recursive `coulombCkp` array. No separately named local Fk/Hk functions are constructed; the sums occur directly in the expansion statements. The ε=0 Bessel formulas are representation bridges to the filled f/h definitions, and the irregular expansion is asymptotic rather than a convergent ε-series.

  [DLMF 33.20.E6](https://dlmf.nist.gov/33.20.E6):
  The coefficients `C_{k,p}` of DLMF 33.20.6: `C_{0,0} = 1`, `C_{k,p} = 0` unless
  `2k ≤ p ≤ 3k`, and `C_{k,p} = (-(2ℓ+p) C_{k-1,p-2} + C_{k-1,p-3})/(4p)` for `k > 0`,
  `2k ≤ p ≤ 3k` (terms with negative second index are `0`).
  `DLMF.Coulomb.coulombCkp` ([definition](DLMF/Coulomb/Energy/Basic.lean#L226)).

### §33.22 Particle Scattering and Atomic and Molecular Spectra

- **Physical potential, reduced mass and wave-number parameters**, [DLMF 33.22.E1](https://dlmf.nist.gov/33.22.E1):
  The Coulomb potential V(s), reduced mass m₁m₂/(m₁+m₂), wave number k, charge scale Z and radial Schrödinger operator are explicit application definitions. No local physical model or dimensional-unit construction is supplied; the exact conversion dictionary remains recorded below.

<!-- retained entry 247 -->
- **k-scaled ρ,η; Z-scaled r,ε; ik-scaled z,κ; Bohr and Rydberg scales**,
  [33.22.4–6 and intervening prose](https://dlmf.nist.gov/33.22.E4):
  no project definitions of these physical scalings, particle masses,
  charges or constants were found. Their mathematical Coulomb arguments
  are supplied directly to the objects above. This is application
  notation, not an omitted numerical approximation implementation.

- **Barrier penetrability and scattering data**, [DLMF 33.22.vi](https://dlmf.nist.gov/33.22.vi):
  The penetrability expression ρ/(Fℓ²+Gℓ²), scattering S-matrix obtained by matching and resonance/Regge poles are application quantities without dedicated local definitions in the Coulomb modules. §§33.23–26 describe methods, tables, approximation references and software for existing functions; they introduce no additional named exact function family or numerical code here.

## Chapter 34 — 3j, 6j, 9j symbols

Expanded review: all 15 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§34.1–34.15 checked; matching headings are §§34.2,
34.4 and 34.6. Names below are in `DLMF.WignerSymbols`.

### §34.1 Special Notation

- **Clebsch–Gordan phase convention**, [DLMF 34.1.E1](https://dlmf.nist.gov/34.1.E1):
  `DLMF.WignerSymbols.clebschGordan` ([source](DLMF/WignerSymbols/Basic.lean#L133)) is the exact phase/√(2j₃+1)-scaled 3j coefficient. The order j₁,m₁,j₂,m₂,j₃,m₃ and the sign of the third projection inside 3j match the displayed convention; it is a separate normalization wrapper, not another independent Racah construction.

  [DLMF 34.1.E1](https://dlmf.nist.gov/34.1.E1):
  DLMF 34.1.1: the Clebsch–Gordan coefficient
  `(j₁ m₁ j₂ m₂ | j₁ j₂ j₃ m₃) = (-1)^{j₁-j₂+m₃} (2j₃+1)^{1/2} (j₁ j₂ j₃; m₁ m₂ -m₃)`.
  `DLMF.WignerSymbols.clebschGordan` ([definition](DLMF/WignerSymbols/Basic.lean#L133)).

### §34.2 Definition: 3 ⁢ j Symbol

<!-- retained entry 248 -->
- **Angular momenta, triangle conditions and projection quantum numbers**,
  [34.2.1–3 and prose](https://dlmf.nist.gov/34.2.E1): `IsAngularMomentum`,
  `IsTriad`, `IsProjection`, `IsAdmissible3j`, with finite range
  `projections`, in [Basic](DLMF/WignerSymbols/Basic.lean#L63).
  j and m are rational, with integrality and parity expressed by predicates;
  `IsTriad` includes the integer-sum restriction, beyond real triangle
  inequalities alone.

- **Admissible finite projection and spin ranges**, [DLMF 34.2.E2](https://dlmf.nist.gov/34.2.E2):
  `DLMF.WignerSymbols.IsNatQ` ([source](DLMF/WignerSymbols/Basic.lean#L60)), `DLMF.WignerSymbols.halfIntegersUpTo` ([source](DLMF/WignerSymbols/Basic.lean#L199)) supplement the projection/triad predicates and projection set. The internal rational factorial and sign functions use floors; their intended factorial/phase interpretation applies to integral admissible arguments, rather than defining Gamma factorials on arbitrary rationals.

<!-- retained entry 249 -->
- **Wigner 3j and triangle coefficient Δ**,
  [34.2.4–5](https://dlmf.nist.gov/34.2.E4): `wigner3j`, `triangleDelta`,
  with `racahTerm3j`, `factQ`, `invFactQ`, `signPow`, in
  [Basic](DLMF/WignerSymbols/Basic.lean#L113). This is the finite Racah
  sum; negative factorial arguments make reciprocal-factorial summands
  zero. Inadmissible projections are extended by zero. The ₃F₂ expression
  34.2.6 is a bridge theorem rather than a second 3j definition.

### §34.3 Basic Properties: 3 ⁢ j Symbol

- **Total angular momentum and Regge transformations**, [DLMF 34.3.E4](https://dlmf.nist.gov/34.3.E4):
  J=j₁+j₂+j₃ is a supplied finite sum, not a separately named local constant. Regge symmetries are the explicit transformed argument arrays of 34.3.11–12 and 34.5.9–10; no independent local Regge-group object is selected.

- **Gaunt integral and Gaunt coefficient**, [DLMF 34.3.E22](https://dlmf.nist.gov/34.3.E22):
  The spherical-harmonic triple integral is Gaunt’s integral, and its exact product-of-two-3j expression is the Gaunt coefficient. They are two sides of the corresponding representation theorem; no independently named local Gaunt function is defined. Spherical harmonics retain the normalization recorded in Chapter 14.

### §34.4 Definition: 6 ⁢ j Symbol

<!-- retained entry 250 -->
- **Wigner 6j**,
  [34.4.1–3](https://dlmf.nist.gov/34.4.E1): `wigner6j`,
  `IsAdmissible6j`, `racahTerm6j` in
  [Basic](DLMF/WignerSymbols/Basic.lean#L155), defined by the single
  Racah sum 34.4.2 and zero outside the four triads. The product-of-four-3j
  definition 34.4.1 is theorem `wigner6j_eq_sum_threeJ` in
  [SixJ](DLMF/WignerSymbols/SixJ.lean), not another defined object;
  the terminating ₄F₃ expression is likewise a bridge.

### §34.5 Basic Properties: 6 ⁢ j Symbol

- **6j recurrence invariants and radical coefficient**, [DLMF 34.5.E12](https://dlmf.nist.gov/34.5.E12):
  Jᵣ=jᵣ(jᵣ+1), Lᵣ=lᵣ(lᵣ+1) are local expressions, and `DLMF.WignerSymbols.sixJRecursionE` ([source](DLMF/WignerSymbols/Basic.lean#L169)) is the square root E(j) of 34.5.13. The nonnegative real-root convention is relevant on admissible spins; it is not an arbitrary signed continuation.

  [DLMF 34.5.E13](https://dlmf.nist.gov/34.5.E13):
  DLMF 34.5.13: the coefficient of the recursion relation 34.5.11,
  `E(j) = ((j² - (j₂-j₃)²)((j₂+j₃+1)² - j²)(j² - (l₂-l₃)²)((l₂+l₃+1)² - j²))^{1/2}`.
  `DLMF.WignerSymbols.sixJRecursionE` ([definition](DLMF/WignerSymbols/Basic.lean#L169)).

### §34.6 Definition: 9 ⁢ j Symbol

<!-- retained entry 251 -->
- **Wigner 9j**, [34.6.1–2](https://dlmf.nist.gov/34.6.E1): `wigner9j`
  in [Basic](DLMF/WignerSymbols/Basic.lean#L178), the finite sum of three
  6j symbols over half-integer j. The six-3j expression is theorem
  `wigner9j_eq_sum_threeJ` in [NineJ](DLMF/WignerSymbols/NineJ.lean).
  No independent three-variable hypergeometric 9j object is defined.

### §34.7 Basic Properties: 9 ⁢ j Symbol

- **9j total phase and symmetry group**, [DLMF 34.7.ii](https://dlmf.nist.gov/34.7.ii):
  The total R is the sum of the nine arguments and determines the (−1)^R factor for odd row/column permutations. The 72 array operations are recorded as symmetry statements, not as a new symbol or separately constructed group action. The auxiliary six-argument factor `DLMF.WignerSymbols.w34_S` ([source](DLMF/WignerSymbols/Basic.lean#L139)) is a local finite phase/weight expression used in symbol identities.

### §34.8 Approximations for Large Parameters

- **Large-parameter angular-momentum angle**, [DLMF 34.8.E2](https://dlmf.nist.gov/34.8.E2):
  DLMF 34.8.2: the angle `θ ∈ [0, π]` of the approximation 34.8.1,
  `cos θ = (j₁(j₁+1) + j₂(j₂+1) - j₃(j₃+1)) / (2 √(j₁(j₁+1) j₂(j₂+1)))`.
  `DLMF.WignerSymbols.largeParameterAngle` ([definition](DLMF/WignerSymbols/Basic.lean#L206)).

### §34.10 Zeros

- **Trivial and nontrivial symbol zeros**, [DLMF 34.10](https://dlmf.nist.gov/34.10):
  Trivial zeros arise from failed angular-momentum/projection admissibility; nontrivial zeros vanish even with admissible data. These are classification predicates expressible using the existing guards and symbol value, without additional local named definitions. §34.11 refers to higher 3nj symbols without supplying new formulas; no local 12j/15j construction was identified. §§34.9,34.12–15 add graphical methods, applications, computation and references rather than additional explicit exact symbol families.

## Chapter 35 — Functions of matrix argument

Expanded review: all 12 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§35.1–35.12 checked; matching headings are the Definition
paragraph of §35.2 and §§35.3(i), 35.4(i), 35.5(i), 35.6(i), 35.7(i),
35.8(i). Names below are in `DLMF.MatrixArgument` unless qualified.

The definitions use real symmetric matrices, the positive-definite cone,
and Lebesgue measure on the independent upper-triangular entries. The
supporting §35.1 notation has actual objects `SymMatrix`, `posDefCone`,
`matrixInterval`, `etr`, `leadingMinor`, `matrixSpectralNorm`,
`orthogonalHaar` in [Basic](DLMF/MatrixArgument/Basic.lean#L76).
The measure is upstream `TauCeti.symmetricLebesgue`; its precise dependency
and normalization are recorded in
[MathlibCoverage](DLMF/MatrixArgument/MathlibCoverage.lean#L12).

### §35.1 Special Notation

- **Symmetric-cone measure, order and integral predicate**, [DLMF 35.1](https://dlmf.nist.gov/35.1):
  Matrix order X>T means X−T positive definite; dX is Lebesgue measure in independent upper-triangular coordinates. `DLMF.MatrixArgument.HasIntegralOn` ([source](DLMF/MatrixArgument/Basic.lean#L90)), `DLMF.MatrixArgument.complexSymmetricOfCoords` ([source](DLMF/MatrixArgument/Basic.lean#L110)) add an integrability-plus-value predicate and the complex symmetric coordinate map to the support objects retained above. The leading minor has value one at j=0 and a local fallback zero for j>m; the spectral norm acts on Euclidean space. DLMF assumes m>0, whereas the Lean definitions also accept m=0.

- **Alternative matrix-function normalizations**, [DLMF 35.1](https://dlmf.nist.gov/35.1):
  Πₘ(a)=Γₘ(a+(m+1)/2), the normalized Bessel J=Aν/Aν(0), and determinant-scaled K/𝒦 notations in the closing prose are normalization dictionaries. No separate local wrappers are defined for these aliases; the determinant factors must be retained when comparing names across sources.

### §35.2 Laplace Transform

<!-- retained entry 252 -->
- **Matrix Laplace transform**, [35.2.1](https://dlmf.nist.gov/35.2.E1):
  `laplaceTransform` in [Basic](DLMF/MatrixArgument/Basic.lean#L306), the
  cone integral with a complex symmetric matrix argument Z.
  `complexSymmetricOfCoords` in
  [Basic](DLMF/MatrixArgument/Basic.lean#L110) parametrizes its independent
  complex entries. The inversion formula 35.2.2 is a theorem, not another
  defined transform.

<!-- retained entry 253 -->
- **Matrix convolution**, [35.2.3](https://dlmf.nist.gov/35.2.E3):
  `matrixConvolution` in [Basic](DLMF/MatrixArgument/Basic.lean#L315),
  integrating over 0<X<T. This is a definition later in the same section,
  outside the first paragraph titled Definition.

### §35.3 Multivariate Gamma and Beta Functions

<!-- retained entry 254 -->
- **Multivariate Γₘ(a), generalized Γₘ(s₁,…,sₘ), and Bₘ(a,b)**,
  [35.3.1–3](https://dlmf.nist.gov/35.3.E1): `multivariateGamma`,
  `multivariateGammaVec`, `multivariateBeta` in
  [Basic](DLMF/MatrixArgument/Basic.lean#L163). These are Gamma products
  or ratios giving the continuations in 35.3.4–5 and 35.3.7; the cone and
  interval integrals of the definition subsection are bridge theorems
  `multivariateGamma_eq_integral`, `multivariateGammaVec_eq_integral`,
  `multivariateBeta_eq_integral` in
  [GammaBeta](DLMF/MatrixArgument/GammaBeta.lean).
  The independent real product `TauCeti.multivariateGamma` is in
  [TauCeti Basic](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/MultivariateGamma/Basic.lean#L64),
  with a real integral theorem in
  [Integral](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/MultivariateGamma/Integral.lean#L169).
  DLMF's integral domains Re a, Re b>(m−1)/2 and Re sⱼ>(j−1)/2
  are essential; totalized products alone do not assert integral convergence.

- **Alternative multivariate beta cone integral**, [DLMF 35.3.E8](https://dlmf.nist.gov/35.3.E8):
  The Ω-integral with |I+X|^{−a−b} is a representation of the same `multivariateBeta`, without a second separately defined integral object. Its convergence conditions Re a,Re b>(m−1)/2 are part of that representation, not supplied by the total Gamma quotient.

### §35.4 Partitions and Zonal Polynomials

<!-- retained entry 255 -->
- **Partition κ, weight |κ|, length ℓ(κ), and a+κ**,
  [opening prose](https://dlmf.nist.gov/35.4.i): `partitions`,
  `partitionLength`, `nextPart` in
  [Basic](DLMF/MatrixArgument/Basic.lean#L139). A partition here is a
  nonincreasing vector `Fin m → ℕ`; its weight and shift are finite-sum
  and pointwise expressions. This representation differs from the
  integer-partition objects in Chapter 26.

<!-- retained entry 256 -->
- **Partitional shifted factorial [a]κ**,
  [35.4.1](https://dlmf.nist.gov/35.4.E1): `partitionalShiftedFactorial`
  in [Basic](DLMF/MatrixArgument/Basic.lean#L155), the product of scalar
  ascending Pochhammer polynomials, with zero-based shift j/2.

<!-- retained entry 257 -->
- **Zonal polynomial Zκ and normalization Zκ(I)**,
  [35.4.2–3](https://dlmf.nist.gov/35.4.E2): `zonalPolynomialAtOne`,
  `zonalPolynomial` in [Basic](DLMF/MatrixArgument/Basic.lean#L188).
  The actual definition uses normalized Haar integration over O(m) and
  powers of leading minors, combining the final determinant factor into
  the product. The intended domain is symmetric T and nonincreasing κ;
  the Lean formula is also evaluable elsewhere. DLMF's Cκ, 𝒴κ and Φκ
  in the closing prose are alternative notation, not extra local objects.

### §35.5 Bessel Functions of Matrix Argument

<!-- retained entry 258 -->
- **Matrix Bessel Aν and Bν**, [35.5.1–3](https://dlmf.nist.gov/35.5.E1):
  `besselA`, `besselB` in [Basic](DLMF/MatrixArgument/Basic.lean#L257).
  A uses its normalized zonal-polynomial series; B is a cone integral with
  the inverse-matrix exponential. The normalization at zero is the reciprocal
  multivariate Gamma expression, not a separately defined constant.
  At exceptional denominator parameters the A-series definition is
  totalized; any continued regularization needs a separate theorem.

### §35.6 Confluent Hypergeometric Functions of Matrix Argument

<!-- retained entry 259 -->
- **Matrix ₁F₁ and Ψ**, [35.6.1–2](https://dlmf.nist.gov/35.6.E1):
  `hyp1F1`, `kummerPsi` in [Basic](DLMF/MatrixArgument/Basic.lean#L238).
  The first wraps the partition series `hypergeometricPFQ`; Ψ is an
  independent cone-integral construction with Re a>(m−1)/2 and T positive
  definite. There is no separate global analytic continuation of that
  integral in this definition layer.

<!-- retained entry 260 -->
- **Matrix Laguerre form Lν⁽γ⁾**, [35.6.3](https://dlmf.nist.gov/35.6.E3):
  `laguerreL` in [Basic](DLMF/MatrixArgument/Basic.lean#L288), the Gamma
  ratio times ₁F₁, with complex degree ν rather than just a polynomial index.

### §35.7 Gaussian Hypergeometric Function of Matrix Argument

<!-- retained entry 261 -->
- **Matrix ₂F₁**, [35.7.1](https://dlmf.nist.gov/35.7.E1): `hyp2F1` in
  [Basic](DLMF/MatrixArgument/Basic.lean#L244), a wrapper for the native
  partition series, interpreted on ‖T‖<1 and nonexceptional c.

<!-- retained entry 262 -->
- **Matrix Jacobi form Pν⁽γ,δ⁾**, [35.7.2](https://dlmf.nist.gov/35.7.E2):
  `jacobiP` in [Basic](DLMF/MatrixArgument/Basic.lean#L296), the stated
  Gamma-ratio/₂F₁ construction; DLMF requires 0<T<I and Re γ>−1.

- **Eigenvalue-coordinate derivatives and hypergeometric PDE**, [DLMF 35.7.E9](https://dlmf.nist.gov/35.7.E9):
  `DLMF.MatrixArgument.coordDeriv` ([source](DLMF/MatrixArgument/Basic.lean#L323)), `DLMF.MatrixArgument.gaussPDEOperator` ([source](DLMF/MatrixArgument/Basic.lean#L328)) construct coordinate derivatives and the differential operator minus abF. The raw operator is used at pairwise distinct eigenvalues; its totalized denominators do not describe a removable extension at coincident eigenvalues by themselves. Orthogonal invariance, analyticity near zero and value one normalize the characterized function; no independent PDE-selected ₂F₁ is defined.

  [DLMF 35.7.E9](https://dlmf.nist.gov/35.7.E9):
  DLMF 35.7.9: the `j`th partial differential operator of the system for `₂F₁` of matrix
  argument, minus its right-hand side `abF`:
  `t_j(1-t_j) ∂²F/∂t_j² - ½ ∑_{k≠j} t_k(1-t_k)/(t_j-t_k) ∂F/∂t_k
    + (c - ½(m-1) - (a+b-½(m-3)) t_j + ½ ∑_{k≠j} t_j(1-t_j)/(t_j-t_k)) ∂F/∂t_j - abF`.
  It is used at points with pairwise distinct `t_k`, where no denominator vanishes.
  `DLMF.MatrixArgument.gaussPDEOperator` ([definition](DLMF/MatrixArgument/Basic.lean#L328)).

### §35.8 Generalized Hypergeometric Functions of Matrix Argument

<!-- retained entry 263 -->
- **Generalized hypergeometric function of matrix argument**,
  [35.8.1](https://dlmf.nist.gov/35.8.E1): `hypergeometricPFQ` in
  [Basic](DLMF/MatrixArgument/Basic.lean#L216), an infinite sum over weights
  of finite sums over partitions. `hyp0F0`, `hyp1F0`, `hyp0F1`, `hyp1F1`,
  `hyp2F1`, `hyp3F2` in the same file are parameter-list wrappers.
  Denominator partitional factorials must not vanish. The convergence
  distinctions p≤q, p=q+1 and p>q+1 are separate properties; a divergent
  totalized sum is not an analytic continuation.

- **Matrix Mellin–Barnes representations**, [DLMF 35.8.v](https://dlmf.nist.gov/35.8.v):
  The multidimensional Mellin–Barnes integrals are referenced as representations of the existing pFq family; no independently named general matrix Barnes integral object is constructed locally. §§35.9–12 supply applications, computation and tables for the same zonal/function families, without new explicit random-matrix density definitions or numerical code.

## Chapter 36 — Integrals with coalescing saddles

Expanded review: all 15 sections reviewed in full, including prose, displayed formulas, table definitions and method/application sections; decimal/graphical material is descriptive only.

Traversal: all §§36.1–36.15 checked; matching headings are §§36.2(i)
and 36.5(i). Names below are in `DLMF.CoalescingSaddles`.

### §36.1 Special Notation

- **Codimension, corank and catastrophe nomenclature**, [DLMF 36.1](https://dlmf.nist.gov/36.1):
  K is the control-space codimension and x₁,…,xK are real controls; x,y,z abbreviate the first three. Cuspoids have one integration variable (corank one); the elliptic/hyperbolic umbilics shown have corank two and codimension three. The fold/cusp/swallowtail names specialize K=1,2,3, without additional independent phase definitions.

### §36.2 Catastrophes and Canonical Integrals

<!-- retained entry 264 -->
- **Cuspoid, elliptic-umbilic and hyperbolic-umbilic normal forms**,
  [36.2.1–3](https://dlmf.nist.gov/36.2.E1): `cuspoidPotential`,
  `ellipticUmbilicPotential`, `hyperbolicUmbilicPotential` in
  [Basic](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L71). Variables are complex,
  control parameters real. K=1,2,3 in `cuspoidPotential` express fold,
  cusp and swallowtail; these are not extra selected functions.

<!-- retained entry 265 -->
- **Canonical integrals ΨK, Ψ⁽ᴴ⁾, Ψ⁽ᴱ⁾**,
  [36.2.4–5](https://dlmf.nist.gov/36.2.E4): `cuspoidIntegral`,
  `hyperbolicUmbilicIntegral`, `ellipticUmbilicIntegral` in
  [Basic](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L126).
  They use absolutely convergent rotated contours or cycles rather than
  the totalized Lebesgue integral of the conditionally convergent real
  oscillation. The contour data are `cuspoidAngle`, `cuspoidContourDir`,
  `cuspoidContour`, `ellipticUmbilicRayDir`, `ellipticUmbilicCycle`,
  `ellipticUmbilicPotentialAB`, `ellipticUmbilicQuadrant` in the same file.
  Alternative one-dimensional contour and Airy representations
  [36.2.6–9](https://dlmf.nist.gov/36.2.E6) are bridge theorems in
  [OscillatoryRepresentations](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L577).
  The F± integrals of 36.2.7 are local expressions in the corresponding
  theorem, not additional globally defined objects.

<!-- retained entry 266 -->
- **Diffraction catastrophes ΨK(x;k), Ψ⁽ᵁ⁾(x;k)**,
  [36.2.10–11](https://dlmf.nist.gov/36.2.E10): `cuspoidDiffraction`,
  `hyperbolicUmbilicDiffraction`, `ellipticUmbilicDiffraction` in
  [Basic](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L159). These use the same
  decaying contours with k in the exponential and the DLMF √k or k factor;
  their intended domain is k>0.

- **Pearcey integral**, [DLMF 36.2.E14](https://dlmf.nist.gov/36.2.E14):
  The Pearcey integral `P(x₂, x₁) = Ψ₂(x₁, x₂)` (DLMF 36.2.14); note the order of the
  arguments.
  `DLMF.CoalescingSaddles.pearcey` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L182)).

### §36.4 Bifurcation Sets

- **Cuspoid Critical Points**, [DLMF 36.4.E1](https://dlmf.nist.gov/36.4.E1):
  The real critical points `t_j(x)` of the cuspoid potential (DLMF 36.4.1):
  real `t` with `∂Φ_K/∂t (t; x) = 0`.
  `DLMF.CoalescingSaddles.cuspoidCriticalPoints` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L189)).

- **Umbilic Critical Points**, [DLMF 36.4.E2](https://dlmf.nist.gov/36.4.E2):
  The real critical points `(s_j(x), t_j(x))` of an umbilic potential (DLMF 36.4.2);
  `Φ` is `ellipticUmbilicPotential` or `hyperbolicUmbilicPotential`.
  `DLMF.CoalescingSaddles.umbilicCriticalPoints` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L228)).

- **Cuspoid Bifurcation Set**, [DLMF 36.4.E3](https://dlmf.nist.gov/36.4.E3):
  The bifurcation (catastrophe) set of the cuspoid of codimension `K` (DLMF 36.4.3): the
  parameters `x` at which a real critical point is degenerate, `∂Φ/∂t = ∂²Φ/∂t² = 0`.
  `DLMF.CoalescingSaddles.cuspoidBifurcationSet` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L195)).

- **Bifurcation strata and cusp/self-intersection geometry**, [DLMF 36.4.E3](https://dlmf.nist.gov/36.4.E3):
  The degeneracy predicates and sets listed here implement critical-point coalescence; the explicit astroid, cusped/smooth sheets, ribs and swallowtail self-intersection of 36.4.5–13 are representations of those sets. No extra selected parametrized surface object is defined. Real critical-point sets are distinct from complex saddles used in the Stokes conditions.

- **Umbilic Bifurcation Set**, [DLMF 36.4.E4](https://dlmf.nist.gov/36.4.E4):
  The bifurcation set of an umbilic catastrophe (DLMF 36.4.4): the parameters `(x, y, z)` at
  which a real critical point has vanishing Hessian determinant.
  `DLMF.CoalescingSaddles.umbilicBifurcationSet` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L234)).

### §36.5 Stokes Sets

<!-- retained entry 267 -->
- **Steepest-descent saddle connection and Stokes sets**,
  [36.5.1 and prose](https://dlmf.nist.gov/36.5.E1):
  `IsSaddleConnection`, `IsSaddleConnection₂`, `cuspoidStokesSet`,
  `umbilicStokesSet`, `cuspoidComplexStokesSet`, `umbilicComplexStokesSet`
  in [Basic](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L255).
  These require distinct critical points connected by a continuous path
  of constant real phase, not just equality of endpoint real parts.
  The first two sets require a real and a nonreal saddle; the separate
  complex-saddle variants exclude conjugate pairs and implement DLMF's
  explicitly identified extensions beyond the main real-saddle convention.

- **Swallowtail Stokes parameter b**, [DLMF 36.5.E3](https://dlmf.nist.gov/36.5.E3):
  The coefficient `B = 10^{-1/3}(2ξ^{4/3} - ξ^{-2/3}/2)` of the swallowtail Stokes curves
  `x = B|y|^{4/3}` at `z = 0`, evaluated at a root `ξ = x_±` of 36.5.4 (DLMF 36.5.3).
  `DLMF.CoalescingSaddles.swallowtailStokesB` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L306)).

- **Selected-root constants and scaled Stokes-sheet variables**, [DLMF 36.5.E3](https://dlmf.nist.gov/36.5.E3):
  B± are defined from the two smallest positive roots of the displayed quintic, while X=x/z²,Y=y/|z|^{3/2} and their umbilic counterparts scale the sheets. The existing polynomial and B(ξ) functions do not select those two roots. Their exact root definitions are mathematical, but the decimal B± and sheet-intersection constants are excluded: numerical. Implicit u,w equations and interval constraints determine branches rather than a globally selected sheet function.

- **Swallowtail Stokes quintic**, [DLMF 36.5.E4](https://dlmf.nist.gov/36.5.E4):
  The quintic `80ξ⁵ - 40ξ⁴ - 55ξ³ + 5ξ² + 20ξ - 1` whose two smallest positive roots `x_±`
  determine the swallowtail Stokes set at `z = 0` (DLMF 36.5.4).
  `DLMF.CoalescingSaddles.swallowtailStokesQuintic` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L300)).

- **Swallowtail Stokes coordinate x**, [DLMF 36.5.E7](https://dlmf.nist.gov/36.5.E7):
  The scaled coordinate `X = 9/20 + 20u⁴ - Y²/(20u²) + 6u² σ` of the swallowtail Stokes set,
  with `σ = sign z` (DLMF 36.5.7).
  `DLMF.CoalescingSaddles.swallowtailStokesX` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L318)).

- **Swallowtail Stokes equation**, [DLMF 36.5.E8](https://dlmf.nist.gov/36.5.E8):
  The left side of the swallowtail Stokes equation (DLMF 36.5.8), with `σ = sign z` and
  `t = swallowtailStokesT u Y σ`:
  `16u⁵ - Y²/(10u) + 4u³σ - (3/10)|Y|σ + 4t⁵ + 2t³σ + |Y|t²`.
  `DLMF.CoalescingSaddles.swallowtailStokesEq` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L324)).

- **Swallowtail Stokes parameter t**, [DLMF 36.5.E9](https://dlmf.nist.gov/36.5.E9):
  The auxiliary quantity `t = -u + (|Y|/(10u) - u² - (3/10) σ)^{1/2}` of the swallowtail Stokes
  set for `z ≠ 0`, with `σ = sign z` (DLMF 36.5.9).
  `DLMF.CoalescingSaddles.swallowtailStokesT` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L312)).

- **Auxiliary quantity of the elliptic umbilic Stokes set (DLMF 36.5.13), with**, [DLMF 36.5.E13](https://dlmf.nist.gov/36.5.E13):
  The auxiliary quantity of the elliptic umbilic Stokes set (DLMF 36.5.13), with
  `η = y/z²`: `w = u - 2/3 + ((2/3 - u)² + |η/6| ((2/3 - u)/u)^{1/2})^{1/2}`.
  `DLMF.CoalescingSaddles.ellipticStokesW` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L333)).

- **Hyperbolic-umbilic Stokes-set coordinates**, [DLMF 36.5.E16](https://dlmf.nist.gov/36.5.E16):
  The function `Y(u, X) = 8u - 24u² + X(u - 1/6)/(u(u - 1/3))^{1/2}` of the hyperbolic umbilic
  Stokes set (DLMF 36.5.16).
  `DLMF.CoalescingSaddles.hyperbolicStokesY` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L339)).

  [DLMF 36.5.E16](https://dlmf.nist.gov/36.5.E16):
  The function `f(u, X) = 16u³ - 4u² - |X|(u/(u - 1/3))^{1/2}/6` of the hyperbolic umbilic
  Stokes set (DLMF 36.5.16).
  `DLMF.CoalescingSaddles.hyperbolicStokesF` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L345)).

- **Auxiliary quantity**, [DLMF 36.5.E21](https://dlmf.nist.gov/36.5.E21):
  The auxiliary quantity
  `w = (1/3 + u)(1 - (1 - |X|/(12u^{1/2}(1/3 + u)^{3/2}))^{1/2})` of the hyperbolic umbilic Stokes
  set (DLMF 36.5.21).
  `DLMF.CoalescingSaddles.hyperbolicStokesW` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L351)).

### §36.6 Scaling Relations

- **Diffraction scaling coordinates**, [DLMF 36.6.E2](https://dlmf.nist.gov/36.6.E2):
  The actual `DLMF.CoalescingSaddles.cuspoidScaledCoords` ([source](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L386)) rescales each control with the cuspoid coordinate exponent. The umbilic vector (xk^{2/3},yk^{2/3},zk^{1/3}) is an expression in its scaling identity, with no separate local wrapper. The exact singularity, coordinate and volume indices below are scaling definitions, not fitted numerical exponents.

  [DLMF 36.6.E2](https://dlmf.nist.gov/36.6.E2):
  The scaled cuspoid coordinates `y(k) = (x_1 k^{γ_{1K}}, …, x_K k^{γ_{KK}})` (DLMF 36.6.2).
  `DLMF.CoalescingSaddles.cuspoidScaledCoords` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L386)).

- **Cuspoid and umbilic singularity indices**, [DLMF 36.6.E3](https://dlmf.nist.gov/36.6.E3):
  The cuspoid singularity index `β_K = K/(2(K+2))` (DLMF 36.6.3).
  `DLMF.CoalescingSaddles.cuspoidSingularityIndex` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L361)).

  [DLMF 36.6.E3](https://dlmf.nist.gov/36.6.E3):
  The umbilic singularity index `β^{(U)} = 1/3` (DLMF 36.6.3).
  `DLMF.CoalescingSaddles.umbilicSingularityIndex` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L365)).

- **Cuspoid and umbilic coordinate scaling indices**, [DLMF 36.6.E4](https://dlmf.nist.gov/36.6.E4):
  The cuspoid coordinate scaling index `γ_{mK} = 1 - m/(K+2)` (DLMF 36.6.4), for `m = 1, …, K`
  (as a function of the natural number `m`).
  `DLMF.CoalescingSaddles.cuspoidCoordinateIndex` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L369)).

  [DLMF 36.6.E4](https://dlmf.nist.gov/36.6.E4):
  The umbilic coordinate scaling indices `(γ_x, γ_y, γ_z) = (2/3, 2/3, 1/3)` (DLMF 36.6.4).
  `DLMF.CoalescingSaddles.umbilicCoordinateIndex` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L374)).

- **Cuspoid and umbilic volume scaling indices**, [DLMF 36.6.E5](https://dlmf.nist.gov/36.6.E5):
  The cuspoid hypervolume scaling index `γ_K = ∑_{m=1}^K γ_{mK}` (DLMF 36.6.5).
  `DLMF.CoalescingSaddles.cuspoidVolumeIndex` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L378)).

  [DLMF 36.6.E5](https://dlmf.nist.gov/36.6.E5):
  The umbilic hypervolume scaling index `γ^{(U)} = ∑ γ_m^{(U)}` (DLMF 36.6.5).
  `DLMF.CoalescingSaddles.umbilicVolumeIndex` ([definition](DLMF/CoalescingSaddles/Basic/CanonicalIntegrals.lean#L382)).

### §36.7 Zeros

- **Inner cusp zero coordinates and indexing conditions**, [DLMF 36.7.E1](https://dlmf.nist.gov/36.7.E1):
  The ordinate `y_m = -√(2π(2m+1))`, `m = 1, 2, …`, of the `m`-th curved row of zeros of the
  Pearcey integral inside the cusp, close to the `y`-axis (DLMF 36.7.1, approximate).
  `DLMF.CoalescingSaddles.cuspInnerZeroY` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L100)).

  [DLMF 36.7.E1](https://dlmf.nist.gov/36.7.E1):
  The abscissae `x^±_{m,n} = √(2/(-y_m)) (2n + 1/2 + (-1)^m/2 ± 1/4) π`, `m = 1, 2, …`,
  `n ∈ ℤ`, of the pairs of zeros of the Pearcey integral inside the cusp (DLMF 36.7.1,
  approximate); the sign `±` is the unit `σ : ℤˣ`.
  `DLMF.CoalescingSaddles.cuspInnerZeroX` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L105)).

- **Asymptotic zero-location models versus exact zero selectors**, [DLMF 36.7.E1](https://dlmf.nist.gov/36.7.E1):
  The curved-row, outer-cusp, ring-plane/lattice and radial functions listed here are explicit asymptotic location formulas. `IsCuspOuterZeroParam` specifies the implicit ξ equation, without choosing its root. None of these functions enumerates exact zeros of the canonical integrals; decimal zero tables and accuracy claims are excluded: numerical.

  [DLMF 36.7.E3](https://dlmf.nist.gov/36.7.E3):
  The equation 36.7.3 for the parameter `ξ_n` of the zeros outside the cusp:
  `3π(8n+5)/(9+8ξ) · ξ^{3/2} = (27/16)(3/2)^{1/2} (ln(1/ξ) + 3 ln(3/2))`. DLMF takes `ξ_n` to be
  "the real solution"; it exists and is unique among `ξ > 0`
  (`existsUnique_cuspOuterZeroParam`).
  `DLMF.CoalescingSaddles.IsCuspOuterZeroParam` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L113)).

- **Outer cusp zero coordinates and indexing conditions**, [DLMF 36.7.E2](https://dlmf.nist.gov/36.7.E2):
  The ordinate `y_n = -(3π(8n+5)/(9+8ξ_n))^{1/2}`, `n = 0, 1, …`, of the zeros just outside the
  cusp (DLMF 36.7.2, approximate), as a function of the parameter `ξ = ξ_n` of 36.7.3.
  `DLMF.CoalescingSaddles.cuspOuterZeroY` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L122)).

  [DLMF 36.7.E2](https://dlmf.nist.gov/36.7.E2):
  The abscissa `x_n = ±(8/27)^{1/2} |y_n|^{3/2} (1 + ξ_n)` of the zeros just outside the cusp
  (DLMF 36.7.2, approximate); the sign `±` is the unit `σ : ℤˣ`.
  `DLMF.CoalescingSaddles.cuspOuterZeroX` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L127)).

- **Elliptic-umbilic zero-ring plane**, [DLMF 36.7.E4](https://dlmf.nist.gov/36.7.E4):
  The planes `z = ±z_n`, `z_n = 3(π(2n - 1/2)/4)^{1/3}`, `n = 1, 2, …`, near which the zero
  rings of the elliptic umbilic integral lie, deep inside the bifurcation set (DLMF 36.7.4,
  approximate; DLMF's decimal form `3.48734 (n - 1/4)^{1/3}` is excluded as numerical).
  `DLMF.CoalescingSaddles.ellipticUmbilicRingPlane` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L133)).

- **Elliptic-umbilic zero lattice and displacement coordinates**, [DLMF 36.7.E5](https://dlmf.nist.gov/36.7.E5):
  The `z` repeat distance `Δz = 9π/(2 z_n²)` of the ring lattice near `z = z_n`
  (DLMF 36.7.5).
  `DLMF.CoalescingSaddles.ellipticUmbilicLatticeDz` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L139)).

  [DLMF 36.7.E5](https://dlmf.nist.gov/36.7.E5):
  The `x` repeat distance `Δx = 6π/z_n` of the ring lattice near `z = z_n` (DLMF 36.7.5).
  `DLMF.CoalescingSaddles.ellipticUmbilicLatticeDx` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L144)).

- **Elliptic-umbilic zero-ring radius equation**, [DLMF 36.7.E6](https://dlmf.nist.gov/36.7.E6):
  The left-hand side of 36.7.6,
  `exp(-2πi((z - z_n)/Δz + 2x/Δx)) (2 exp(-6πix/Δx) cos(2√3πy/Δx) + 1)`, with `z_n`, `Δz`, `Δx`
  from 36.7.4–36.7.5; the zeros of `Ψ^{(E)}` near `z = z_n` are approximated by the solutions of
  `ellipticUmbilicRingEquation n x y z = √3` (DLMF 36.7.6).
  `DLMF.CoalescingSaddles.ellipticUmbilicRingEquation` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L148)).

- **Elliptic-umbilic zero-ring count**, [DLMF 36.7.E7](https://dlmf.nist.gov/36.7.E7):
  The number `n_max(m) = ⌊(256/13) m - 269/52⌋` of zero rings in the `m`-th row of a symmetry
  plane, before the transition to hairpins (DLMF 36.7.7, an empirical count).
  `DLMF.CoalescingSaddles.ellipticUmbilicRingCount` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L161)).

- **Elliptic-umbilic planar zero radius**, [DLMF 36.7.E8](https://dlmf.nist.gov/36.7.E8):
  The leading term `3((2n-1)π/(4|sin(3θ/2)|))^{2/3}` of the radius of the `n`-th zero of
  `Ψ^{(E)}(r cos θ, r sin θ, 0)` (DLMF 36.7.8).
  `DLMF.CoalescingSaddles.ellipticUmbilicPlaneZeroRadius` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L166)).

### §36.8 Convergent Series Expansions

- **Cuspoid power-series coefficients**, [DLMF 36.8.E2](https://dlmf.nist.gov/36.8.E2):
  The coefficients `a_n(x)` of the cuspoid series 36.8.1, defined by the recurrence 36.8.2:
  `a_0 = 1`, `a_{n+1} = (i/(n+1)) ∑_{p=0}^{min(n, K-1)} (p+1) x_{p+1} a_{n-p}`. In Lean the index
  `p` runs over `Fin (min (n+1) K)` (the same range, and empty when `K = 0`), and DLMF's `x_{p+1}`
  is `x p`. They are the Maclaurin coefficients of `exp(i ∑ₘ xₘ tᵐ)`.
  `DLMF.CoalescingSaddles.cuspoidSeriesCoeff` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L58)).

- **Elliptic-umbilic series factor F**, [DLMF 36.8.E5](https://dlmf.nist.gov/36.8.E5):
  The functions `f_n(ζ, ζ')` of 36.8.5 (DLMF writes `f_n(ζ, ζ̄)` and evaluates at
  `ζ' = ζ̄`):
  `f_n = c_n(ζ)c_n(ζ')Ai(ζ)Bi(ζ') + c_n(ζ)d_n(ζ')Ai(ζ)Bi'(ζ') + d_n(ζ)c_n(ζ')Ai'(ζ)Bi(ζ')
    + d_n(ζ)d_n(ζ')Ai'(ζ)Bi'(ζ')`.
  `DLMF.CoalescingSaddles.ellipticUmbilicSeriesF` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L84)).

- **Coupled Airy-derivative polynomial recurrence**, [DLMF 36.8.E6](https://dlmf.nist.gov/36.8.E6):
  `DLMF.CoalescingSaddles.umbilicSeriesCD` ([source](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L70)) is the actual paired recurrence whose projections are `umbilicSeriesC` and `umbilicSeriesD`. These cₙ,dₙ also encode higher derivatives of Airy solutions; the two-variable `ellipticUmbilicSeriesF` retains independent complex inputs and is specialized to conjugate inputs in DLMF. The series identities represent existing canonical integrals rather than independently defining additional continuations.

  [DLMF 36.8.E6](https://dlmf.nist.gov/36.8.E6):
  The polynomials `c_n(t)` of 36.8.6: `c_0 = 1`, `c_{n+1} = c_n' + t d_n`.
  `DLMF.CoalescingSaddles.umbilicSeriesC` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L76)).

  [DLMF 36.8.E6](https://dlmf.nist.gov/36.8.E6):
  The polynomials `d_n(t)` of 36.8.6: `d_0 = 0`, `d_{n+1} = c_n + d_n'`.
  `DLMF.CoalescingSaddles.umbilicSeriesD` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L80)).

### §36.10 Differential Equations

- **Canonical differential operators and contour moments**, [DLMF 36.10.E1](https://dlmf.nist.gov/36.10.E1):
  `DLMF.CoalescingSaddles.cuspoidMoment` ([source](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L42)), `DLMF.CoalescingSaddles.hyperbolicUmbilicMoment` ([source](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L49)) are actual rotated-contour moment integrals used to realize repeated derivatives. Polynomial substitution −i∂x into the phase derivatives defines the operator equations; 36.10.17 is the paraxial wave equation. No separate general differential-operator algebra or PDE-selected canonical function is constructed.

### §36.11 Leading-Order Asymptotics

- **Leading-order stationary-phase sum of 36.11.2**, [DLMF 36.11.E1](https://dlmf.nist.gov/36.11.E1):
  The leading-order stationary-phase sum of 36.11.2,
  `√(2π) ∑ⱼ exp(i(Φ_K(tⱼ; x) + ¼π(-1)^{j+K+1})) |∂²Φ_K(tⱼ; x)/∂t²|^{-1/2}`, over the real critical
  points `t₁ < t₂ < ⋯` of `Φ_K(·; x)` (DLMF 36.11.1). The sign `(-1)^{j+K+1}` of DLMF is written as
  the sign of `∂²Φ_K/∂t²(tⱼ)`: the leading coefficient of `∂Φ_K/∂t` is positive and its degree is
  `K + 1`, so at simple critical points the signs of `∂²Φ_K/∂t²` alternate and that at `t₁` is
  `(-1)^K`. The sum is a `finsum` over the (finite) set of real critical points.
  `DLMF.CoalescingSaddles.cuspoidStationaryPhaseSum` ([definition](DLMF/CoalescingSaddles/Basic/AuxiliaryData.lean#L174)).

### §36.12 Uniform Approximation of Integrals

- **Uniform normal-form map and interpolation coefficients**, [DLMF 36.12.E4](https://dlmf.nist.gov/36.12.E4):
  The analytic change u(t;y), offset A(y), control map x(y), scaled z(y;k), coefficients aₘ, Pₘₙ and Gₙ in 36.12.4–10 are defined by critical-point correspondence and interpolation. No local function selects a general normal-form mapping or these coefficients. Square roots are positive for the all-real critical-point configuration and continued analytically elsewhere; principal roots taken independently would not encode that convention.

- **Two-saddle phase difference and amplitude factors**, [DLMF 36.12.E12](https://dlmf.nist.gov/36.12.E12):
  The mean phase f̃, values g±, curvatures f±″ and Δ=[3(f₋−f₊)/4]^{2/3} define the K=1 uniform approximation. Δ is chosen positive for real saddles and negative for the complex pair, with the curvature ratios continued from positive real values. These are expressions in the theorem hypotheses, without a separately selected local branch map.

### §36.13 Kelvin’s Ship-Wave Pattern

- **Kelvin-wave integral, phase, stationary angles and wake scale**, [DLMF 36.13.E1](https://dlmf.nist.gov/36.13.E1):
  The model integral z(φ,ρ), nondimensional radius ρ=gr/V², phase f, stationary angles θ±, exact critical angle arcsin(1/3), dispersion Hamiltonian and amplitudes u,v of 36.13.1–7 are mathematical application definitions. No dedicated local ship-wave or dispersion construction is supplied; the Airy functions entering their asymptotic representation already exist. The integral is an exact definition of the model, while its interpretation as wave height is approximate.

### §36.14 Other Physical Applications

- **Caustics and asymptotic integration contours**, [DLMF 36.14.i](https://dlmf.nist.gov/36.14.i):
  A caustic is the structurally stable focal envelope/singularity of a ray family, corresponding here to a bifurcation set. No generic ray-family/caustic structure is defined locally. §36.15 describes finite and deformed contour computation, with valleys at infinity where exp(iΦ) decays; the exact decaying contours used in the function definitions are recorded at §36.2, without acquiring numerical quadrature code.

## Expanded review coverage and checks

All 872 section pages have been reviewed in chapter/section order. Each chapter’s expanded-review line records its complete section count; subsections, prose definitions, exact coefficients and mathematical table conventions were inspected as well as displayed equations. Application definitions and exact numerical-method constructions are recorded descriptively, while decimal values, graphical results and implementation-only helpers are not additional mathematical definitions.

The 1,153 grouped correspondences retain all 267 earlier entries and add 886 consolidated groups. Local source paths and line anchors, public local declaration names, DLMF equation/prose anchors and ordering by the first cited source were checked against the pinned Lean sources and cached DLMF HTML. Source order uses actual paragraph positions, including interspersed unnumbered definitions. The checks do not establish theorems used by admitted choice specifications.

## Earlier survey coverage and interpretation

The following historical counts retain the earlier title-based traversal. The expanded review above includes the full contents of the section pages, not only those matching headings.

The following counts are section pages / pages with a matching heading /
matching headings. Nested headings on the same page count separately; an
inspected parent and child do not create duplicate mathematical entries.

- Chapter 1: 18 / 4 / 5.
- Chapter 2: 11 / 1 / 1.
- Chapter 3: 12 / 0 / 0.
- Chapter 4: 48 / 5 / 5.
- Chapter 5: 24 / 1 / 1.
- Chapter 6: 21 / 1 / 1.
- Chapter 7: 25 / 3 / 3.
- Chapter 8: 28 / 4 / 7.
- Chapter 9: 20 / 1 / 1.
- Chapter 10: 77 / 6 / 7.
- Chapter 11: 16 / 3 / 3.
- Chapter 12: 21 / 0 / 0.
- Chapter 13: 32 / 2 / 2.
- Chapter 14: 34 / 4 / 4.
- Chapter 15: 20 / 1 / 1.
- Chapter 16: 27 / 2 / 2.
- Chapter 17: 19 / 0 / 0.
- Chapter 18: 42 / 8 / 10.
- Chapter 19: 39 / 2 / 2.
- Chapter 20: 16 / 1 / 1.
- Chapter 21: 11 / 1 / 1.
- Chapter 22: 22 / 3 / 4.
- Chapter 23: 24 / 2 / 2.
- Chapter 24: 21 / 1 / 1.
- Chapter 25: 21 / 4 / 5.
- Chapter 26: 22 / 11 / 11.
- Chapter 27: 22 / 1 / 1.
- Chapter 28: 36 / 6 / 6.
- Chapter 29: 22 / 2 / 2.
- Chapter 30: 18 / 3 / 3.
- Chapter 31: 18 / 2 / 2.
- Chapter 32: 17 / 2 / 2.
- Chapter 33: 26 / 3 / 3.
- Chapter 34: 15 / 3 / 3.
- Chapter 35: 12 / 7 / 7.
- Chapter 36: 15 / 2 / 2.

Only Chapters 3, 12 and 17 had no matching title. The earlier catalogue labelled supplementary entries in Chapters 4, 7, 9, 12, 16, 17, 31 and 32 as complementary; those entries did not change its heading counts. The earlier catalogue did not cover every other heading. The expanded inventory above reviews all section contents while continuing to distinguish mathematical definitions from implementation-only helpers.

The source check distinguishes native series, actual integrals, selected
continuations, predicate characterizations and aliases. Primary Mathieu,
Lamé and angular spheroidal existence/specification results cited above were
also checked with Lean's compiled axiom inventory and use no `sorryAx`.
Noninteger Mathieu continuation, the selected Heun disk continuation and
Stieltjes polynomials, and the Lambert branch-family existence have the
admission qualifications stated in their entries. This is not a complete
axiom audit of every bridge theorem in the catalogue.

The clearest uncovered named families in the matching sections are the Kelvin
functions and their continuous phases, the cylindrical-Bessel continuous
modulus/phase objects, and the principal Mathieu exponent selector. There are
also narrower domain/branch gaps, exceptional-parameter continuation questions,
and the explicitly recorded empty-path convention for Narayana numbers.
Missing physical scalings in §33.22(ii) are application notation; numerical
approximations and tabulated decimal values have not been added to the project.
