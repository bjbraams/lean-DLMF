# DLMF definitions and their Lean counterparts

This inventory surveys the sections and subsections whose headings contain
“Definition” or “Definitions”, in chapter and section order, in the live
[NIST Digital Library of Mathematical Functions](https://dlmf.nist.gov/)
(version 1.2.8, checked 2026-10-29). It includes definitions in prose and tables,
not just numbered formulas. A chapter with no such heading can still contain
definitions elsewhere; complementary entries below are identified explicitly.
Chapter 3 is included in this documentary survey although numerical algorithms
are outside the project's formalization scope. All 872 top-level section pages
were visited sequentially in chapter/section order; 102 pages contain 111
matching headings, including nested headings. There are 267 grouped entries;
several entries cover multiple related mathematical objects. The per-chapter traversal lines
identify those headings; the counts below make the scan reviewable.

Lean names refer to actual definitions, abbreviations, structures or predicates
in this checkout and its pinned dependencies. An alternative representation
that is only a theorem is identified as a bridge, rather than as another defined
function. Several Lean objects can represent the same DLMF function on different
domains or with different constructions. Aliases are distinguished from those
mathematical alternatives. This is a correspondence inventory, not a claim that
all the associated properties or equivalence theorems have been proved.

Unless an entry says otherwise, Lean's infinite sums, products, integrals,
division and chosen continuations are totalized. The DLMF interpretation applies
on the stated convergence domain and away from exceptional parameters; assigning
a Lean value outside that domain does not supply a DLMF analytic continuation.

## Chapter 1 — Algebraic and analytic methods

Traversal: all §§1.1–1.18 checked; matching headings are the square-matrix
paragraph in §1.2(vi), §1.8(i), §1.15(i), §1.15(iv), and §1.17(iv).

### §1.2(vi): Special properties and definitions relating to square matrices

- **Determinant**, [1.2.58–59](https://dlmf.nist.gov/1.2.E59): Mathlib
  `Matrix.det`, defined by the signed permutation sum in
  [Determinant/Basic](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean#L63).
  The permutations and their signs are `Equiv.Perm` and `Equiv.Perm.sign`.
- **Inverse; singular and nonsingular matrices**, [1.2.60 and adjacent prose](https://dlmf.nist.gov/1.2#Px12):
  Mathlib's matrix inverse `A⁻¹` in
  [NonsingularInverse](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean#L150),
  and `IsUnit A` for invertibility. Over a field, singularity is `A.det = 0`;
  Lean totalizes the inverse at singular matrices.
- **Trace**, [1.2.62](https://dlmf.nist.gov/1.2.E62): Mathlib `Matrix.trace`
  in [Trace](.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Trace.lean#L43).
- **Commuting matrices and commutator**, [1.2.66 and preceding prose](https://dlmf.nist.gov/1.2.E66):
  `Commute A B` and the ring Lie bracket `⁅A, B⁆ = A * B - B * A`.
  [MathlibCoverage](DLMF/AlgebraicAnalytic/Algebra/MathlibCoverage.lean#L203)
  records the upstream bracket identification.
- **Euclidean operator norm**, [1.2.67](https://dlmf.nist.gov/1.2.E67):
  Mathlib's scoped `Matrix.Norms.L2Operator` instance and the norm of the corresponding
  continuous linear map. This requires the Euclidean operator norm, not an
  arbitrary matrix norm; see the explicit use in
  [Matrices](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L216).
- **Eigenvalue and eigenvector**, [1.2.70–72](https://dlmf.nist.gov/1.2.E70):
  `Module.End.HasEigenvalue` and `Module.End.HasEigenvector`, applied to the
  matrix linear map, in
  [Eigenspace/Basic](.lake/packages/mathlib/Mathlib/LinearAlgebra/Eigenspace/Basic.lean#L435).
- **Linear independence, non-defective/defective matrices, and eigenvalue
  multiplicity**, [prose surrounding 1.2.73](https://dlmf.nist.gov/1.2.E73):
  `LinearIndependent` expresses the eigenvector condition; local statements use
  an invertible matrix of eigenvectors and a diagonal matrix in
  [Matrices](DLMF/AlgebraicAnalytic/Algebra/Matrices.lean#L241).
  There is no separate local `NonDefective` predicate. Repeated diagonal
  entries are counted by their finite index set; algebraic multiplicity can
  instead be expressed using the characteristic polynomial's root multiplicity.
- **Matrix exponential and exponential of the trace**, [1.2.76–77](https://dlmf.nist.gov/1.2.E76):
  Mathlib `NormedSpace.exp`, applied to matrices, and `Complex.exp A.trace`.
  There is no separate local `etr` wrapper here.

### §1.8(i): Definitions and elementary properties

- **Fourier series and trigonometric Fourier coefficients**, [1.8.1–2](https://dlmf.nist.gov/1.8.E2):
  `DLMF.AlgebraicAnalytic.fourierCosCoeff` and `fourierSinCoeff` in
  [Fourier/Defs](DLMF/AlgebraicAnalytic/Fourier/Defs.lean#L41).
  They accept complex-valued functions of a real argument and use DLMF's
  `1/π` normalization; the constant term is `a₀/2`.
- **Exponential Fourier coefficients**, [1.8.3–4](https://dlmf.nist.gov/1.8.E4):
  `DLMF.AlgebraicAnalytic.fourierExpCoeff` in
  [Fourier/Defs](DLMF/AlgebraicAnalytic/Fourier/Defs.lean#L55).
  Mathlib `fourierCoeffOn` is another integral construction; the bridge
  `fourierExpCoeff_eq_fourierCoeffOn` accounts for the interval and period.
  Fourier-series sums are expressions built from these coefficients, not
  additional definitions in this file.
- **Lebesgue constants**, [1.8.8](https://dlmf.nist.gov/1.8.E8):
  `DLMF.AlgebraicAnalytic.lebesgueConstant` in
  [Fourier/Defs](DLMF/AlgebraicAnalytic/Fourier/Defs.lean#L59).

### §1.15(i), (iv): Definitions for series and integrals

- **Partial sums**, [1.15.1](https://dlmf.nist.gov/1.15.E1):
  `DLMF.AlgebraicAnalytic.seriesPartialSum` in
  [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L56).
- **Abel summability of a series**, [1.15.2–3](https://dlmf.nist.gov/1.15.E3):
  `DLMF.AlgebraicAnalytic.HasAbelSum` in
  [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L62),
  including summability for every real `0 < x < 1` and the limit from below.
- **Cesàro summability**, [1.15.4–5](https://dlmf.nist.gov/1.15.E5):
  `cesaroMean` and `HasCesaroSum` in
  [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L67),
  in namespace `DLMF.AlgebraicAnalytic`.
- **General Cesàro summability**, [1.15.6–7](https://dlmf.nist.gov/1.15.E7):
  `DLMF.AlgebraicAnalytic.cesaroMeanOfOrder` and `HasCesaroSumOfOrder`
  in [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L76).
  The definition accepts all real orders; DLMF's interpretation assumes `α > -1`.
- **Borel summability**, [1.15.8–9](https://dlmf.nist.gov/1.15.E9):
  `DLMF.AlgebraicAnalytic.HasBorelSum` in
  [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L89).
  This is the exponential generating function of the partial sums, not of the
  original terms; convergence for every nonnegative real argument is included.
- **Abel summability of an integral**, [1.15.29–30](https://dlmf.nist.gov/1.15.E30):
  `DLMF.AlgebraicAnalytic.HasAbelIntegral` in
  [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L154).
- **Cesàro summability of an integral**, [1.15.31–32](https://dlmf.nist.gov/1.15.E32):
  `DLMF.AlgebraicAnalytic.HasCesaroIntegral` in
  [Summability/Defs](DLMF/AlgebraicAnalytic/Summability/Defs.lean#L160).

### §1.17(iv): Mathematical definitions

[This heading](https://dlmf.nist.gov/1.17.iv) contains bibliographic guidance
about rigorous treatments of the delta representations in earlier subsections;
it introduces no further mathematical definition. The delta distribution itself
is defined in §1.16, outside this title-based scope.

## Chapter 2 — Asymptotic approximations

Traversal: all §§2.1–2.11 checked; the matching section is §2.1, including its
five subsections.

### §2.1: Definitions and elementary properties

- **Asymptotic equivalence**, [2.1.1](https://dlmf.nist.gov/2.1.E1):
  Mathlib `Asymptotics.IsEquivalent` in
  [AsymptoticEquivalent](.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/AsymptoticEquivalent.lean#L77).
  The normed additive formulation uses a little-o difference; the quotient
  formulation requires the usual eventual nonvanishing interpretation.
- **Little-o and big-O**, [2.1.2–3](https://dlmf.nist.gov/2.1.E2):
  Mathlib `Asymptotics.IsLittleO`, `IsBigO` and the explicit-bound `IsBigOWith`
  in [Defs](.lake/packages/mathlib/Mathlib/Analysis/Asymptotics/Defs.lean#L73).
  A within-set limiting filter describes DLMF's approach in `X`; a principal
  filter describes a bound on the whole set. These norm inequalities also cover
  points where the comparison function vanishes.
- **Poincaré expansion at infinity**, [2.1.13–15](https://dlmf.nist.gov/2.1.E13):
  `DLMF.AsymptoticApproximations.HasPoincareExpansion` in
  [Basics/Defs](DLMF/AsymptoticApproximations/Basics/Defs.lean#L49), specializing
  `Asymptotics.HasAsymptoticExpansion` to inverse powers and the cobounded
  filter restricted to `X`. A bounded `X` gives a vacuous Lean predicate;
  DLMF assumes an unbounded approach set.
- **Poincaré expansion at a finite point**, [2.1.16](https://dlmf.nist.gov/2.1.E16):
  `DLMF.AsymptoticApproximations.HasPoincareExpansionAt` in
  [Basics/Defs](DLMF/AsymptoticApproximations/Basics/Defs.lean#L56).
  The related general formal-series construction is
  `Asymptotics.HasAsymptoticPowerSeries` in
  [AsymptoticInversion](DLMFMathlib/Analysis/Asymptotics/AsymptoticInversion.lean#L69).
- **Uniform Poincaré expansion**, [2.1.18 and §2.1(iv) prose](https://dlmf.nist.gov/2.1.iv):
  `DLMF.AsymptoticApproximations.HasUniformPoincareExpansion` in
  [Basics/Defs](DLMF/AsymptoticApproximations/Basics/Defs.lean#L64).
  The product filter makes both the bound and the threshold uniform in the
  parameter. There is no separately named finite-point uniform version.
- **Asymptotic scale**, [2.1.19](https://dlmf.nist.gov/2.1.E19):
  `Asymptotics.IsAsymptoticScale` in
  [AsymptoticExpansion](DLMFMathlib/Analysis/Asymptotics/AsymptoticExpansion.lean#L56).
- **Generalized asymptotic expansion**, [2.1.20–21](https://dlmf.nist.gov/2.1.E20):
  `DLMF.AsymptoticApproximations.HasGeneralizedAsymptoticExpansion` in
  [Basics/Defs](DLMF/AsymptoticApproximations/Basics/Defs.lean#L74).
  Its summands can be functions rather than constant multiples of the scale.
  `Asymptotics.HasAsymptoticExpansion` is the constant-coefficient construction;
  uniform generalized expansions can be expressed by a product filter, but
  have no additional local wrapper.

## Chapter 3 — Numerical methods

Traversal: all §§3.1–3.12 checked. No heading contains “Definition” or
“Definitions”. This does not mean the chapter contains no definitions: it
introduces numerical methods under their own headings. Those methods have no
claimed Lean counterpart in this inventory and are outside acquisition scope.

## Chapter 4 — Elementary functions

Traversal: all §§4.1–4.48 checked; matching headings are §4.2, §4.14,
§4.23(i), §4.28, and §4.37(i).

### §4.2: Definitions

- **General logarithm, principal logarithm, and the two banks of the closed
  principal cut**, [4.2.1–7](https://dlmf.nist.gov/4.2.i):
  `DLMF.Elementary.generalLogValues`, `logSheet`, `closedLogValues`, and
  `logBranchCut` in [LogExpBasic](DLMF/Elementary/LogExpBasic.lean#L58);
  Mathlib `Complex.log` and `Real.log` are the single-valued complex and real
  functions, defined in
  [Complex/Log](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean#L30)
  and [Log/Basic](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean).
  `Complex.log` selects the upper bank of the negative axis;
  `closedLogValues` retains both values. No separate arbitrary-path integral
  logarithm is defined.
- **Logarithm to base a**, [4.2.8](https://dlmf.nist.gov/4.2.E8):
  `DLMF.Elementary.complexLogb` in
  [LogExpBasic](DLMF/Elementary/LogExpBasic.lean#L323), and Mathlib `Real.logb`
  in [Log/Base](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Base.lean#L44).
  The complex definition divides principal logarithms and inherits their cuts.
- **Natural base e and exponential**, [4.2.12–13](https://dlmf.nist.gov/4.2.E12),
  [4.2.19](https://dlmf.nist.gov/4.2.E19): Mathlib `Real.exp 1`, `Real.exp`,
  `Complex.exp` in
  [Complex/Exponential](.lake/packages/mathlib/Mathlib/Analysis/Complex/Exponential.lean#L63),
  and the general Banach-algebra `NormedSpace.exp` in
  [Normed/Algebra/Exponential](.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/Exponential.lean).
  The decimal values in 4.2.11, 4.2.17 and 4.2.18 are numerical, not additional
  definition objects in this inventory.
- **General and principal powers**, [4.2.26–28](https://dlmf.nist.gov/4.2.E26):
  `DLMF.Elementary.generalPowerValues` and `closedPowerValues` in
  [LogExpBasic](DLMF/Elementary/LogExpBasic.lean#L366);
  Mathlib `Complex.cpow` selects the principal logarithm, `Real.rpow` treats
  real powers, and ordinary natural/integer powers cover the single-valued
  cases. The definitions are in
  [Pow/Complex](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean)
  and [Pow/Real](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean).
  `Complex.sqrt` in [RCLike/Sqrt](.lake/packages/mathlib/Mathlib/Analysis/RCLike/Sqrt.lean#L26)
  is the principal square root mentioned in 4.2.37.
  The set-valued local constructions preserve DLMF's two-bank convention.

### Complementary §4.13: Lambert W-function

- **Lambert integer branches Wₖ and upper/lower cut values**,
  [4.13.1 and branch prose](https://dlmf.nist.gov/4.13.E1):
  `DLMF.Elementary.lambertW`, `lambertWLower`, with
  `LambertBranchFamily` and `lambertPrincipalDomain`, in
  [BranchesAndCalculus](DLMF/Elementary/LambertW/BranchesAndCalculus.lean#L393).
  The family is selected using `exists_lambertBranchFamily` in
  [BranchesAndCalculus](DLMF/Elementary/LambertW/BranchesAndCalculus.lean#L343),
  which remains admitted. The structure specifies analytic domains,
  basepoint normalization and upper-side boundary values; `lambertWLower`
  applies conjugation and k→−k. Nonprincipal values at zero are totalized.
- **Wright omega and tree T**,
  [4.13.1_2–1_3](https://dlmf.nist.gov/4.13.E1_2):
  `DLMF.Elementary.wrightOmega`, `treeT` in
  [BranchesAndCalculus](DLMF/Elementary/LambertW/BranchesAndCalculus.lean#L400).
  Omega selects the integer unwinding branch using the imaginary part of z;
  T is −W₀(−z). Both inherit the admitted branch-family construction.

### §4.14: Definitions and periodicity

- **Sine and cosine**, [4.14.1–2](https://dlmf.nist.gov/4.14.E1): Mathlib
  `Complex.sin`, `Complex.cos`, `Real.sin`, and `Real.cos` in
  [Complex/Trigonometric](.lake/packages/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean#L29).
- **Tangent, cosecant, secant and cotangent**, [4.14.4–7](https://dlmf.nist.gov/4.14.E4):
  Mathlib `Complex.tan`, `Complex.cot`, `Real.tan`, `Real.cot`, and
  `DLMF.Elementary.csc`, `sec` in
  [DirectIdentities](DLMF/Elementary/Trigonometric/DirectIdentities.lean#L79).
  The real cosecant/secant are expressible as inverse sine/cosine; there is no
  additional local real wrapper. Quotients have totalized values at poles.

### §4.23(i): General definitions of inverse trigonometric functions

- **General arcsine, arccosine, arctangent, arccosecant, arcsecant and
  arccotangent**, [4.23.1–6](https://dlmf.nist.gov/4.23.i):
  `DLMF.Elementary.arcsinGeneral`, `arccosGeneral`, `arctanGeneral`,
  `arccscGeneral`, `arcsecGeneral`, and `arccotGeneral` in
  [InverseBranches](DLMF/Elementary/Trigonometric/InverseBranches.lean#L66).
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

### §4.28: Definitions and periodicity of hyperbolic functions

- **Hyperbolic sine, cosine and tangent**, [4.28.1–4](https://dlmf.nist.gov/4.28.E1):
  Mathlib `Complex.sinh`, `Complex.cosh`, `Complex.tanh`, `Real.sinh`,
  `Real.cosh`, `Real.tanh` in
  [Complex/Trigonometric](.lake/packages/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean#L49).
- **Hyperbolic cosecant, secant and cotangent**, [4.28.5–7](https://dlmf.nist.gov/4.28.E5):
  `DLMF.Elementary.csch`, `sech`, and `coth` in
  [IdentitiesAndSeries](DLMF/Elementary/Hyperbolic/IdentitiesAndSeries.lean#L33).
  Real restrictions are expressions through these quotients, without separate
  local real definitions.

### §4.37(i): General definitions of inverse hyperbolic functions

- **General inverse sinh, cosh, tanh, csch, sech and coth**, [4.37.1–6](https://dlmf.nist.gov/4.37.i):
  `DLMF.Elementary.arcsinhValues`, `arccoshValues`, `arctanhValues`,
  `arccschValues`, `arcsechValues`, and `arccothValues` in
  [IdentitiesAndSeries](DLMF/Elementary/Hyperbolic/IdentitiesAndSeries.lean#L69).
  Principal logarithmic formulas are separately defined there as `arcsinh`,
  `arccosh`, `arctanh`, `arccsch`, `arcsech`, `arccoth`.
  Mathlib `Real.arsinh` in
  [Arsinh](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Arsinh.lean#L54)
  is an independent real construction. The local complex
  objects select branches; their value sets encode the full inverse relations.

## Chapter 5 — Gamma function

Traversal: all §§5.1–5.24 checked; the matching section is §5.2.

### §5.2: Definitions

- **Gamma**, [Euler integral 5.2.1 and continuation prose](https://dlmf.nist.gov/5.2.i):
  Mathlib `Complex.GammaIntegral` and `Complex.Gamma` in
  [Gamma/Basic](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean#L110),
  and `Real.Gamma`. `GammaIntegral` is the actual half-line integral;
  `Gamma` extends it by recurrence and is totalized to zero at poles.
  The reciprocal gamma is `1 / Complex.Gamma z`, not a separate local definition.
- **Psi/digamma**, [5.2.2](https://dlmf.nist.gov/5.2.E2): Mathlib
  `Complex.digamma = logDeriv Complex.Gamma` in
  [Digamma](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Digamma.lean#L48),
  and the independently defined real quotient `Real.digamma` in
  [Gamma/Digamma](DLMF/Gamma/Digamma.lean#L40).
- **Euler's constant**, [exact limit in 5.2.3](https://dlmf.nist.gov/5.2.E3):
  Mathlib `Real.eulerMascheroniConstant` in
  [EulerMascheroni](.lake/packages/mathlib/Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean).
  The accompanying decimal expansion is
  numerical and is excluded.
- **Pochhammer symbol/rising factorial**, [5.2.4–5](https://dlmf.nist.gov/5.2.E4):
  Mathlib `ascPochhammer` evaluated at the base, from
  [Polynomial/Pochhammer](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Pochhammer.lean);
  `DLMF.Hypergeometric.poch`
  is an abbreviation for this in [Hypergeometric/Basic](DLMF/Hypergeometric/Basic.lean#L31).
  The gamma quotient is an identity away from poles, not its definition.
- **Falling factorial and Lah numbers**, [prose and 5.2.9](https://dlmf.nist.gov/5.2.E9):
  Mathlib `descPochhammer` in
  [Polynomial/Pochhammer](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Pochhammer.lean)
  and natural falling factorial `Nat.descFactorial` in
  [Factorial/Basic](.lake/packages/mathlib/Mathlib/Data/Nat/Factorial/Basic.lean#L332);
  `DLMF.Elementary.fallingPower` in
  [LogExpAnalysis](DLMF/Elementary/LogExpAnalysis.lean#L755) is the complex product.
  Lah numbers are expressible by the displayed binomial/factorial formula;
  no separately named Lah-number definition is used here.

## Chapter 6 — Exponential, logarithmic, sine and cosine integrals

Traversal: all §§6.1–6.21 checked; the matching section is §6.2.

### §6.2: Definitions and interrelations

All local names below, including names beginning `Real.`, are under
`DLMF.Confluent`.

- **Principal exponential integral E₁**, [6.2.1–2](https://dlmf.nist.gov/6.2.E1):
  `genExpIntE 1 z` in [ExpIntegral](DLMF/Confluent/ExpIntegral.lean#L48);
  `genExpIntEOnLog 1 w` retains arbitrary sheets. These are incomplete-gamma
  constructions; the horizontal-ray and half-line integrals are bridge theorems.
- **Entire complementary exponential integral Ein**, [6.2.3](https://dlmf.nist.gov/6.2.E3):
  series `expIntEin` in [ExpIntegrals/Basic](DLMF/ExpIntegrals/Basic.lean#L29)
  and independent real interval integral `Real.expIntEin` in
  [ExpIntegral](DLMF/Confluent/ExpIntegral.lean#L145).
- **Real Ei and logarithmic integral li**, [6.2.5–8](https://dlmf.nist.gov/6.2.E5):
  `Real.expIntEi` and `Real.logIntLi` in
  [ExpIntegrals/Basic](DLMF/ExpIntegrals/Basic.lean#L64), using the continued
  series and `Ei(log x)`. The principal-value integrals are theorem characterizations,
  not separate functions. DLMF excludes `Ei(0)` and restricts this li definition
  to `x > 1`.
- **Sine integral Si and shifted si**, [6.2.9–10](https://dlmf.nist.gov/6.2.E9):
  complex series `sinInt` and shift `sinIntTail` in
  [ExpIntegrals/Basic](DLMF/ExpIntegrals/Basic.lean#L34);
  independent real interval-integral `Real.sinInt` in
  [ExpIntegral](DLMF/Confluent/ExpIntegral.lean#L352).
- **Cosine integral Ci and entire Cin**, [6.2.11–13](https://dlmf.nist.gov/6.2.E11):
  `cosIntCin`, `cosInt` in [ExpIntegrals/Basic](DLMF/ExpIntegrals/Basic.lean#L39),
  and the real integral/logarithm constructions `Real.cosIntCin`, `Real.cosInt`
  in [ExpIntegral](DLMF/Confluent/ExpIntegral.lean#L400).
  Complex Ci uses the principal logarithm; it does not encode both banks as a set.
- **Hyperbolic integrals Shi and Chi**, [6.2.15–16](https://dlmf.nist.gov/6.2.E15):
  `sinhInt` and `coshInt` in [ExpIntegrals/Basic](DLMF/ExpIntegrals/Basic.lean#L54),
  respectively an entire series and a principal-logarithm-plus-series definition.
- **Auxiliary f and g**, [6.2.17–18](https://dlmf.nist.gov/6.2.E17):
  `expIntAuxF` and `expIntAuxG` in
  [ExpIntegrals/Basic](DLMF/ExpIntegrals/Basic.lean#L74).

## Chapter 7 — Error functions, Dawson's and Fresnel integrals

Traversal: all §§7.1–7.25 checked; matching headings are §7.2, §7.18(i),
and §7.19(i).

### §7.2: Definitions

The local complex functions in this section are in namespace `DLMF.Confluent`.

- **erf and erfc**, [7.2.1–2](https://dlmf.nist.gov/7.2.E1):
  `erf` and `erfc` in [Confluent/Basic](DLMF/Confluent/Basic.lean#L540)
  use the Kummer series and its complement. Independent real interval-integral
  definitions are `TauCeti.Real.erf` and `TauCeti.Real.erfc` in
  [TauCeti/Erf](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/Erf.lean#L62);
  local `erf_ofReal` and `erfc_ofReal` are bridges.
  The independent real integral `DLMF.Confluent.Real.generalizedErrorIntegral 2`
  in [InverseGeneralized](DLMF/ErrorFunctions/InverseGeneralized.lean#L26)
  differs by the factor 2/√π. The §7.1 notation variants `scaledErf`,
  `gaussianCdf`, `gaussianTail` in
  [Basic](DLMF/ErrorFunctions/Basic.lean#L606) are argument/normalization
  wrappers, not new integral constructions.
- **Faddeeva/probability function w**, [7.2.3](https://dlmf.nist.gov/7.2.E3):
  `faddeevaW` in [ErrorFunctions/Basic](DLMF/ErrorFunctions/Basic.lean#L27).
- **Dawson F**, [7.2.5](https://dlmf.nist.gov/7.2.E5):
  `dawsonF` in [ErrorFunctions/Basic](DLMF/ErrorFunctions/Basic.lean#L32),
  using a straight-segment primitive. `dawsonPrimitive` is the corresponding
  unscaled primitive in the same file.
  `DLMF.Confluent.Real.generalizedDawsonIntegral 2` in
  [InverseGeneralized](DLMF/ErrorFunctions/InverseGeneralized.lean#L30)
  is an independent real integral of exp(t²); multiplying it by exp(−x²)
  gives Dawson's normalization.
- **Fresnel tail, C and S**, [7.2.6–8](https://dlmf.nist.gov/7.2.E6):
  `fresnelTail`, `fresnelCosInt`, `fresnelSinInt` in
  [ErrorFunctions/Basic](DLMF/ErrorFunctions/Basic.lean#L37).
  C and S use the DLMF phase `πt²/2`; the tail is its entire continued
  expression `(1+i)/2 - C - iS`. The rescaled `fresnelC1`, `fresnelS1`,
  `fresnelC2`, `fresnelS2` in the same file are different argument normalizations.
- **Fresnel auxiliary f and g**, [7.2.10–11](https://dlmf.nist.gov/7.2.E10):
  `fresnelAuxFComplex` and `fresnelAuxGComplex` in
  [ErrorFunctions/Basic](DLMF/ErrorFunctions/Basic.lean#L52).
- **Goodwin–Staton integral**, [7.2.12](https://dlmf.nist.gov/7.2.E12):
  `goodwinStatonG` in [ErrorFunctions/Basic](DLMF/ErrorFunctions/Basic.lean#L62),
  an actual half-line integral, interpreted on the slit plane.

### Complementary §7.17(i): Inverse-error notation

- **Inverse erf and erfc**, [7.17.1](https://dlmf.nist.gov/7.17.E1):
  upstream `_root_.Real.erfInv` in
  [TauCeti/Erf](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/Erf.lean#L251)
  is the inverse order isomorphism of `TauCeti.Real.erf`, with zero outside
  (−1,1). `DLMF.Confluent.Real.invErf` is a wrapper around it;
  `DLMF.Confluent.Real.invErfc x = Real.invErf (1-x)` in
  [InverseGeneralized](DLMF/ErrorFunctions/InverseGeneralized.lean#L174)
  has the corresponding intended domain (0,2). No complex inverse branch
  is selected by these real functions.

### §7.18(i): Definition of repeated integrals of erfc

- **Repeated complementary error integrals**, [7.18.1–2](https://dlmf.nist.gov/7.18.E1):
  `DLMF.Confluent.iteratedErfc` in
  [Repeated](DLMF/ErrorFunctions/Repeated.lean#L28), with integer index `n ≥ -1`.
  It handles `-1` as the Gaussian and nonnegative indices by a shifted
  half-line integral; indices below `-1` are artificial zero values.
  `gaussianProbabilityHh` in the same file is a related independent Gaussian
  moment normalization, with exponent `-(z+t)²/2`.

### §7.19(i): Definitions of Voigt functions

- **Voigt U, V, and line-broadening H**, [7.19.1–4](https://dlmf.nist.gov/7.19.E1):
  `DLMF.Confluent.Real.voigtU`, `voigtV`, and `voigtH` in
  [Voigt](DLMF/ErrorFunctions/Voigt.lean#L25).
  These are actual real whole-line integrals. Their mathematical domains are
  `t > 0` and `a > 0`; 7.19.3 is a complex-erfc bridge, not a fourth definition.

## Chapter 8 — Incomplete gamma and related functions

Traversal: all §§8.1–8.28 checked; matching headings are §8.2 (including (i)),
§8.17(i)/(vii), §8.19(i), and §8.21(i)/(ii). Nested matching headings are counted
once when discussing their mathematical content.

### §8.2: Definitions and basic properties

- **Lower incomplete gamma**, [8.2.1](https://dlmf.nist.gov/8.2.E1):
  `DLMF.Confluent.lowerIncGamma` in
  [Confluent/Basic](DLMF/Confluent/Basic.lean#L639), using a Kummer series;
  `lowerIncGammaOnLog` in [IncompleteGamma/Basic](DLMF/IncompleteGamma/Basic.lean#L32)
  retains the logarithmic sheet. `TauCeti.lowerIncompleteGamma` in
  [TauCeti/IncompleteGamma](.lake/packages/TauCeti/TauCeti/Analysis/SpecialFunctions/IncompleteGamma.lean#L115)
  is an independent real integral for positive shape and nonnegative endpoint;
  it truncates negative endpoints to zero and assigns zero for nonpositive shape.
  At nonpositive integral parameters, the
  ordinary local formula has totalized values rather than pole data.
- **Upper incomplete gamma**, [8.2.2](https://dlmf.nist.gov/8.2.E2):
  `DLMF.Confluent.upperIncGamma` in
  [Confluent/Relations](DLMF/Confluent/Relations.lean#L108), using Tricomi U;
  `upperIncGammaOnLog` in [IncompleteGamma/Basic](DLMF/IncompleteGamma/Basic.lean#L28)
  continues on the logarithmic plane, also at integral parameters. Integral
  representations are bridge theorems, not additional functions.
- **Normalized P and Q**, [8.2.4](https://dlmf.nist.gov/8.2.E4):
  quotient definitions `DLMF.Statistical.normIncGammaP`, `normIncGammaQ` in
  [Statistical/IncompleteGamma](DLMF/Statistical/IncompleteGamma.lean#L44);
  parameter-continuation definitions `DLMF.Confluent.normIncGammaPContinued`,
  `normIncGammaQContinued`, `normIncGammaPOnLog`, `normIncGammaQOnLog` in
  [IncompleteGamma/Basic](DLMF/IncompleteGamma/Basic.lean#L37).
  The continued functions are materially different at nonpositive integral
  parameters. `TauCeti.regularizedGamma` is the real integral quotient
  representing P for positive real shape; `1 - regularizedGamma` represents Q
  on that domain without another definition.
- **Tricomi's entire γ-star**, [8.2.6–7](https://dlmf.nist.gov/8.2.E6):
  `DLMF.Statistical.scIncGamma` in
  [Statistical/IncompleteGamma](DLMF/Statistical/IncompleteGamma.lean#L176),
  using the regularized confluent series rather than the singular quotient.

### §8.17(i), (vii): Incomplete beta definitions and addendum

- **Incomplete beta Bₓ**, [8.17.1](https://dlmf.nist.gov/8.17.E1):
  `DLMF.Statistical.Real.incBeta` in
  [Statistical/IncompleteBeta](DLMF/Statistical/IncompleteBeta.lean#L51)
  is an interval integral with real endpoint and complex parameters;
  `DLMF.Statistical.incBeta` in
  [IncompleteGamma/Beta](DLMF/IncompleteGamma/Beta.lean#L27) is a principal
  hypergeometric continuation, with a separate value at `z = 1`.
- **Normalized incomplete beta Iₓ**, [8.17.2](https://dlmf.nist.gov/8.17.E2):
  `DLMF.Statistical.Real.normIncBetaI` is the integral quotient;
  `DLMF.Statistical.normIncBetaI` is the continued regularized formula in
  [IncompleteGamma/Beta](DLMF/IncompleteGamma/Beta.lean#L31), preserving
  a removable `a = 0` specialization. They should not be identified at
  exceptional parameters merely by totalized division.
- **Complete beta**, [8.17.3](https://dlmf.nist.gov/8.17.E3): Mathlib
  `Complex.betaIntegral` in
  [Gamma/Beta](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L60).
  The gamma quotient is a bridge on its proper parameter domain. The addendum
  [8.17.24](https://dlmf.nist.gov/8.17.E24) is a series identity for I, not a new definition.

### §8.19(i): Generalized exponential integral

- **Eₚ**, [8.19.1–4](https://dlmf.nist.gov/8.19.i):
  `DLMF.Confluent.genExpIntE` in
  [ExpIntegral](DLMF/Confluent/ExpIntegral.lean#L48),
  `genExpIntEOnLog` and `genExpIntEExtended` in
  [ExponentialIntegral](DLMF/IncompleteGamma/ExponentialIntegral.lean#L29).
  `OnLog` retains the sheet; `Extended` assigns `1/(p-1)` at zero, whose
  DLMF meaning requires `Re p > 1`. The integrals in 8.19.2–4 have theorem
  representations, with no separately defined integral-based Eₚ object.

### §8.21(i), (ii): General and principal generalized sine/cosine integrals

- **Lower Si(a,z), Ci(a,z) and upper si(a,z), ci(a,z)**,
  [8.21.1–2](https://dlmf.nist.gov/8.21.E1) and
  [principal-value prose](https://dlmf.nist.gov/8.21.ii):
  `DLMF.Confluent.genSinIntOnLog`, `genCosIntOnLog`,
  `genSinIntTailOnLog`, `genCosIntTailOnLog`, `genSinInt`, `genCosInt`,
  `genSinIntTail`, `genCosIntTail` in
  [GammaRepresentations](DLMF/IncompleteGamma/SineCosine/GammaRepresentations.lean#L29).
  Lower functions use convergent series on logarithmic coordinates; upper
  functions use continued upper gamma. Principal functions specialize `w = log z`.
  Lower parameter poles remain exceptional; the upper functions are entire
  in the parameter. The ordinary Chapter 6 functions are different
  specializations and shifts, not naming aliases.

## Chapter 9 — Airy and related functions

Traversal: all §§9.1–9.20 checked; the matching heading is §9.8(i).

### §9.8(i): Definitions of modulus and phase

- **Airy moduli M, N and continuous phases θ, φ**, [9.8.1–8 and branch prose](https://dlmf.nist.gov/9.8.i):
  `DLMF.Airy.airyModulus`, `airyDerivModulus`, `airyPhase`, and
  `airyDerivPhase` in
  [Representations](DLMF/Airy/ModulusPhase/Representations.lean#L31).
  The phases are defined by integrals, with values `π/6` and `-π/6` at zero,
  so they retain the continuous branches rather than principal arctangents.
  DLMF restricts this section to real `x ≤ 0`.

Complementary fundamental definitions: [§9.2](https://dlmf.nist.gov/9.2)
is titled “Differential Equation”, not “Definitions”. Its Ai, Bi and derivatives
are `DLMF.Airy.airyAi`, `airyBi`, `airyAiDeriv`, `airyBiDeriv` in
[Basic](DLMF/Airy/Basic.lean#L143), constructed from regularized ₀F₁;
real restrictions `airyAiReal`, `airyBiReal`, `airyAiDerivReal`,
`airyBiDerivReal` are in [Framework](DLMF/Airy/Framework.lean#L26).
Integral formulas are bridge theorems, not alternative public Ai/Bi definitions.

## Chapter 10 — Bessel functions

Traversal: all §§10.1–10.77 checked; matching headings are §10.2,
§10.18(i), §10.25, §10.47, §10.61 (including (i)), and §10.68(i).

### §10.2: Definitions

- **Bessel equation**, [10.2.1](https://dlmf.nist.gov/10.2.E1): expressible
  through `DLMF.Struve.besselResidual` with the homogeneous sign convention in
  [Struve/Basic](DLMF/Struve/Basic.lean#L85), or directly as a derivative identity.
  `DLMF.Bessel.IsRealBesselSolution` in
  [SturmZeros](DLMF/Bessel/SturmZeros.lean#L357) is a real differential-system predicate.
- **Jν**, [10.2.2](https://dlmf.nist.gov/10.2.E2): Mathlib
  `Complex.besselJ` in
  [Bessel](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Bessel.lean#L55),
  a principal-power times regularized ₀F₁ definition. Local
  `besselJ_eq_regularized` in [Basic](DLMF/Bessel/Basic.lean#L39)
  is a bridge, not another definition.
- **Yν, including integral orders**, [10.2.3–4](https://dlmf.nist.gov/10.2.E3):
  `DLMF.Bessel.besselY` in [Basic](DLMF/Bessel/Basic.lean#L47), with order limits
  at integers. The separately defined `besselYLaplace` is an auxiliary
  integral in Y representations in
  [YIntegralRep](DLMF/Bessel/YIntegralRep.lean#L254), not another definition of
  the whole Y function.
- **Hankel H¹ and H²**, [defining asymptotics 10.2.5–6](https://dlmf.nist.gov/10.2.E5):
  `DLMF.Bessel.hankelH1`, `hankelH2` in
  [SecondKind](DLMF/Bessel/SecondKind.lean#L516), defined as `J ± iY`.
- **General cylinder function Cν**, [§10.2(ii) prose](https://dlmf.nist.gov/10.2.ii):
  finite constant linear combinations of the preceding functions; no separate
  local definition or structure for this notation.

The functions above use a single principal-power convention, with separate
logarithmic constructions `airyBesselJOnLog`, `airyBesselYOnLog`,
`airyHankel1OnLog`, and `airyHankel2OnLog` in
[Airy/Framework](DLMF/Airy/Framework.lean#L85) when sheets are needed.
These logarithmic formulas must be used with their parameter hypotheses.

### §10.18(i): Definitions of modulus and phase

- **Bessel Mν, Nν, θν and φν**, [10.18.1–3](https://dlmf.nist.gov/10.18.i):
  no corresponding named Lean objects found. Norms of H¹ and its derivative
  give the moduli, but `Complex.arg` alone would not give the prescribed
  continuous phases with the limits at zero.

### §10.25: Definitions of modified Bessel functions

- **Modified Bessel equation**, [10.25.1](https://dlmf.nist.gov/10.25.E1):
  expressible through the sign choice of `DLMF.Struve.besselResidual`; no
  separate local homogeneous-equation predicate is needed by the library.
- **Iν and Kν**, [10.25.2–3](https://dlmf.nist.gov/10.25.E2):
  `DLMF.Bessel.besselI`, `besselK` in [Modified](DLMF/Bessel/Modified.lean#L28).
  I uses the regularized ₀F₁ series; K uses the I-connection formula with
  order limits at integers. `airyBesselIOnLog`, `airyBesselKOnLog` in
  [Airy/Framework](DLMF/Airy/Framework.lean#L85) retain logarithmic arguments.
  `besselKMoment 0` in [KIntegralRep](DLMF/Bessel/KIntegralRep.lean#L127)
  is the independently defined whole-line integral moment used in integral
  representations; normalization to K is a theorem, not an alias.
- **General modified cylinder function Zν**, [§10.25(ii) prose](https://dlmf.nist.gov/10.25.ii):
  represented by constant linear combinations of I and `exp(νπi) K`;
  no separate named object.

### §10.47: Definitions and basic properties of spherical Bessel functions

- **Spherical jₙ and modified i¹ₙ**, [10.47.3](https://dlmf.nist.gov/10.47.E3),
  [10.47.7](https://dlmf.nist.gov/10.47.E7):
  `DLMF.sphericalJ`, `DLMF.sphericalI` in
  [Framework](DLMF/Core/Framework.lean#L173), defined by regularized series
  that include their removable values at zero. These avoid interpreting a
  totalized square-root quotient as the value at zero.
- **Spherical yₙ, h¹ₙ, h²ₙ**,
  [10.47.4–6](https://dlmf.nist.gov/10.47.E4),
  are cases 2, 3 and 4 of `DLMF.Spheroidal.spheroidalPsi` in
  [Spheroidal/Basic](DLMF/Spheroidal/Basic.lean#L407). These actual
  square-root-times-cylinder definitions carry the principal branch and
  exclude zero in their intended domains. There are no extra public
  spherical-Y/H aliases.
- **Modified spherical i²ₙ and kₙ**,
  [10.47.8–9](https://dlmf.nist.gov/10.47.E8): no separate corresponding
  definitions found. They can be expressed using half-integer I and K,
  but those expressions do not supply named spherical objects or endpoint
  conventions.

### §10.61(i), §10.68(i): Kelvin functions and their modulus/phase functions

- **berν, beiν, kerν and keiν**, [10.61.1–2](https://dlmf.nist.gov/10.61.E1):
  no named Lean equivalents found. They are the real/imaginary components of
  the specified rotated J and K expressions, with real order and `x ≥ 0`.
- **Kelvin Mν, Nν, θν and φν**, [10.68.1–2 and branch prose](https://dlmf.nist.gov/10.68.i):
  no named equivalents found. The continuous phases are fixed by large-argument
  asymptotics; they are not simply principal arguments.

## Chapter 11 — Struve and related functions

Traversal: all §§11.1–11.16 checked; matching headings are §11.2,
§11.9(i), and §11.10(i).

### §11.2: Definitions

- **Struve H and modified Struve L**, [11.2.1–2](https://dlmf.nist.gov/11.2.E1):
  `DLMF.Struve.struveH`, `struveL`, their entire cores `struveHCore`,
  `struveLCore`, and logarithmic versions `struveHOnLog`, `struveLOnLog`
  in [Basic](DLMF/Struve/Basic.lean#L170). The core removes the fractional
  power; `OnLog` records its sheet. These are genuine different constructions
  of the branch factor, not real/imaginary components.
- **Auxiliary Struve K and M**, [11.2.5–6](https://dlmf.nist.gov/11.2.E5):
  `DLMF.Struve.struveK`, `struveM` in
  [Basic](DLMF/Struve/Basic.lean#L494), the differences `H-Y` and `L-I`.
  Struve K is distinct from modified Bessel K. Its independently defined
  Laplace integral is `DLMF.Bessel.besselYLaplace` in
  [YIntegralRep](DLMF/Bessel/YIntegralRep.lean#L254), corresponding to
  [11.5.2](https://dlmf.nist.gov/11.5.E2) on the proper convergence domain.
- **Struve and modified Struve equations**, [11.2.7–10](https://dlmf.nist.gov/11.2.E7):
  `DLMF.Struve.struveEquation` and `IsStruveSolutionOn` in
  [Basic](DLMF/Struve/Basic.lean#L505), with a Boolean selecting the modified sign.

### §11.9(i): Lommel definitions

- **Lommel denominator product aₖ and lower sμν**, [11.9.3–4](https://dlmf.nist.gov/11.9.E3):
  `DLMF.Struve.lommelA`, `lommelS`, and the parameter predicate `LommelRegular`
  in [Lommel](DLMF/Struve/Lommel.lean#L35).
- **Capital Lommel Sμν**, [11.9.5 and limiting-value prose](https://dlmf.nist.gov/11.9.E5):
  `DLMF.Struve.lommelCapitalRegular` and `lommelCapital` in
  [Lommel](DLMF/Struve/Lommel.lean#L51). The former is the connection formula;
  the latter chooses its parameter limit, including exceptional orders.

### §11.10(i): Anger–Weber definitions

- **Anger J and Weber E**, [11.10.1–2](https://dlmf.nist.gov/11.10.E1):
  `DLMF.Struve.angerJ`, `weberE` in
  [IntegralAndSeries](DLMF/Struve/AngerWeber/IntegralAndSeries.lean#L36),
  actual finite-interval integrals, entire in both complex arguments.
- **Associated Anger–Weber A**, [11.10.4](https://dlmf.nist.gov/11.10.E4):
  `DLMF.Struve.angerARegular` and `angerA` in
  [IntegralAndSeries](DLMF/Struve/AngerWeber/IntegralAndSeries.lean#L278).
  The quotient `(Anger J - Bessel J)/sin(πν)` is extended by order limits;
  the half-line integral is a bridge on its stated convergence domain.

## Chapter 12 — Parabolic cylinder functions

Traversal: all §§12.1–12.21 checked; no heading contains “Definition” or
“Definitions”. Complementary fundamental definitions are recorded here from
[§12.2](https://dlmf.nist.gov/12.2) and [§12.14](https://dlmf.nist.gov/12.14),
whose titles are “Differential Equations” and “The Function W(a,x)”.

- **U(a,z), Dν(z), and even/odd canonical solutions**, [12.2.2–5](https://dlmf.nist.gov/12.2.E2):
  `DLMF.Confluent.pcfU`, `pcfD`, `pcfEven`, `pcfOdd`, and their separately
  defined derivatives `pcfUDeriv`, `pcfEvenDeriv`, `pcfOddDeriv` in
  [EquationAndIntegrals](DLMF/Confluent/ParabolicCylinder/EquationAndIntegrals.lean#L36).
  The construction uses entire Kummer functions; integral representations
  are bridges on smaller parameter domains.
- **V(a,z)**, [§12.2(i), 12.2.8–9](https://dlmf.nist.gov/12.2.E8):
  `DLMF.Confluent.pcfV`, `pcfVDeriv`, `pcfVZero`, `pcfVDerivZero` in
  [WronskiansAndConnections](DLMF/Confluent/ParabolicCylinder/WronskiansAndConnections.lean#L328).
- **U-bar and modulus/phase F, θ, G, ψ**, [12.2.21–23](https://dlmf.nist.gov/12.2.E21):
  `DLMF.Confluent.pcfUBar`, `pcfUBarDeriv`, `pcfF`, `pcfTheta`,
  `pcfG`, and `pcfPsi` in [Basic](DLMF/ParabolicCylinder/Basic.lean#L172).
  U-bar means a gamma-scaled V, not complex conjugation; its parameter poles
  are excluded in mathematical uses.
- **W(a,x), initial values and canonical even/odd solutions**,
  [12.14.1–2](https://dlmf.nist.gov/12.14.E1),
  [12.14.8–10](https://dlmf.nist.gov/12.14.E8):
  `DLMF.Confluent.pcfW`, `pcfWZero`, `pcfWDerivZero`, `pcfWEven`,
  `pcfWOdd`, and `pcfWDeriv` in
  [Solutions](DLMF/ParabolicCylinder/Weber/Solutions.lean#L34).
  W has a real parameter and a complex argument; its series construction
  fixes DLMF's real normalization.

## Chapter 13 — Confluent hypergeometric functions

Traversal: all §§13.1–13.32 checked; matching sections are §13.2 and §13.14.

### §13.2: Definitions and basic properties

- **Kummer M = ₁F₁ and regularized M**, [13.2.2–4](https://dlmf.nist.gov/13.2.E2):
  `DLMF.Confluent.kummerM` in [Basic](DLMF/Confluent/Basic.lean#L42),
  the ordinary series, and Mathlib `Complex.regularizedHGFun {a} {b} z`
  in [RegularizedHypergeometric](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean#L173).
  Ordinary M has exceptional lower parameters; the regularized series retains
  their removable values. The local ordinary series is not an analytic
  extension through those parameter poles.
- **Tricomi U**, [defining asymptotic 13.2.6](https://dlmf.nist.gov/13.2.E6):
  `DLMF.Confluent.kummerUConnection`, `kummerU`, and `kummerUOnLog` in
  [Basic](DLMF/Confluent/Basic.lean#L411). The principal U chooses order
  limits at integral b; the raw connection formula and the logarithmic
  formula represent U only for nonintegral b. Thus `OnLog` does not by itself
  supply integral-b continuation. U's half-line integral is a theorem representation.

### §13.14: Definitions and basic properties of Whittaker functions

- **Whittaker M and W**, [13.14.2–3](https://dlmf.nist.gov/13.14.E2):
  `DLMF.Confluent.whittakerM`, `whittakerW`, `whittakerMOnLog`, and
  `whittakerWOnLog` in [Whittaker](DLMF/Confluent/Whittaker.lean#L31).
  Principal W uses the continued U. The logarithmic W connection expression
  requires `2μ` nonintegral; it is not the full continuation at half-integer μ.
- **Regularized Whittaker M**, [limiting normalization 13.14.7](https://dlmf.nist.gov/13.14.E7):
  `DLMF.Confluent.regularizedWhittakerM` in
  [Whittaker](DLMF/Confluent/Whittaker.lean#L36), using the regularized series
  before multiplication. It is different from dividing totalized ordinary M
  by gamma at exceptional parameters.

## Chapter 14 — Legendre and related functions

Traversal: all §§14.1–14.34 checked; matching headings are §14.3,
§14.20(i), §14.21, and §14.30(i).

### §14.3 and §14.21: Real and complex definitions

- **Ferrers P**, [14.3.1](https://dlmf.nist.gov/14.3.E1):
  `DLMF.Legendre.ferrersP` in [Basic](DLMF/Legendre/Basic.lean#L55), with
  real argument in `(-1,1)` and complex degree/order. The polynomial
  specialization `ferrersPNat` in [Harmonics](DLMF/Legendre/Harmonics.lean#L30)
  is independently defined by derivatives of the Legendre polynomial.
- **Ferrers Q and auxiliary w₁,w₂**, [14.3.2](https://dlmf.nist.gov/14.3.E2),
  [14.3.13–14](https://dlmf.nist.gov/14.3.E13):
  `DLMF.Legendre.ferrersQ`, `ferrersW1`, `ferrersW2` in
  [QuadraticFerrers](DLMF/Legendre/Associated/QuadraticFerrers.lean#L57).
  The quadratic hypergeometric construction avoids division by `sin(πμ)`
  at integer orders. `LegendreQRegular` records the excluded `ν+μ` values.
- **Associated Legendre P, Q and Olver Q-bold**,
  [14.3.6–10](https://dlmf.nist.gov/14.3.E6) and
  [complex continuation prose in §14.21(i)](https://dlmf.nist.gov/14.21.i):
  `DLMF.Legendre.associatedP`, `associatedQ`, `olverQ`, and branch factor
  `legendreBranchPower` in
  [QuadraticFerrers](DLMF/Legendre/Associated/QuadraticFerrers.lean#L29).
  Q-bold is regularized before multiplication by `Gamma(ν+μ+1)`; it remains
  meaningful where classical Q has parameter poles. Separate logarithms of
  `z-1` and `z+1` preserve continuation from `z > 1` on the DLMF cut.
  The order-zero functions `legendreP` in [Basic](DLMF/Legendre/Basic.lean#L50)
  and `legendreQ` in [SecondKind](DLMF/Legendre/SecondKind.lean#L109)
  are separate definitions with their own representations.
- **Olver's regularized hypergeometric F-bold**, [14.3.3](https://dlmf.nist.gov/14.3.E3):
  `DLMF.Hypergeometric.regularizedGaussHG`, as detailed in Chapter 15.

### §14.20(i): Conical definitions

- **Conical/Mehler functions and Dunster Q-hat**, [14.20.1–3](https://dlmf.nist.gov/14.20.E1):
  `DLMF.Legendre.conicalP` and `conicalQHat` in
  [Conical](DLMF/Legendre/Conical.lean#L26). Parameters are ordered `τ, μ, x`,
  with degree `-1/2+iτ` and order `-μ`. Q-hat excludes `τ=0` with positive
  half-odd-integral μ. For `x > 1`, the conical solution is instead the
  specialization of `associatedP`, not the Ferrers wrapper.

### §14.30(i): Spherical and spheroidal harmonics

- **Spherical harmonics Yₗₘ**, [14.30.1](https://dlmf.nist.gov/14.30.E1):
  `DLMF.Legendre.sphericalHarmonicNonneg` and `sphericalHarmonic` in
  [Harmonics](DLMF/Legendre/Harmonics.lean#L51). The latter handles signed m,
  includes the DLMF phase convention, and gives zero when `|m| > l`.
  The general harmonic-polynomial objects
  `DLMF.SphericalHarmonics.IsHarmonicHomogeneous` in
  [SphericalHarmonics/Basic](DLMF/SphericalHarmonics/Basic.lean#L44)
  are related objects, not aliases for the angular functions.
- **Surface, tesseral and sectorial harmonics**, [14.30.2 and prose](https://dlmf.nist.gov/14.30.E2):
  `DLMF.Legendre.surfaceHarmonic` in
  [Harmonics](DLMF/Legendre/Harmonics.lean#L126), with a sine/cosine flag.
  Tesseral and sectorial are conditions on `|m|`, without separate wrappers.
- **Prolate/oblate harmonics and scaled oblate R,T**, [§14.30(i) prose](https://dlmf.nist.gov/14.30.i):
  specializations of `associatedP` and `associatedQ`; scaled functions are
  `DLMF.Legendre.scaledOblateR`, `scaledOblateT` in
  [Harmonics](DLMF/Legendre/Harmonics.lean#L939).

## Chapter 15 — Hypergeometric function

Traversal: all §§15.1–15.20 checked; the matching section is §15.2.

### §15.2: Definitions and analytical properties

- **Gauss F = ₂F₁**, [15.2.1](https://dlmf.nist.gov/15.2.E1): Mathlib
  `ordinaryHypergeometric` and `ordinaryHypergeometricSeries` in
  [OrdinaryHypergeometric](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/OrdinaryHypergeometric.lean#L71)
  are the native series constructions. On the principal cut plane the ordinary
  continued value is expressed locally as `Gamma c * regularizedGaussHG a b c z`;
  there is no separate local ordinary-continuation function name.
- **Regularized F-bold**, [15.2.2](https://dlmf.nist.gov/15.2.E2): Mathlib
  `Complex.regularizedGaussHGFun` in
  [RegularizedHypergeometric](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean#L360)
  is the series; `DLMF.Hypergeometric.regularizedGaussHGIntegral` is Euler's
  interval integral and `regularizedGaussHG` is its parameter-shift continuation
  in [ArgumentContinuation](DLMF/Hypergeometric/ArgumentContinuation.lean#L143).
  The continued function has mathematical domain `ℂ \ [1,∞)`; the integral
  construction needs `Re b > 0`, `Re(c-b) > 0`. None of these objects alone
  records both banks as a set.
- **Terminating exceptional-parameter interpretation**,
  [15.2.4–6](https://dlmf.nist.gov/15.2.E4): terminating sums can be expressed
  with `gaussHGCoeff` in [Basic](DLMF/Hypergeometric/Basic.lean#L148).
  There is no named two-variable limiting object distinguishing the two
  orders of parameter limits in 15.2.5 and 15.2.6; those interpretations must
  not be inferred from a totalized series or quotient.

## Chapter 16 — Generalized hypergeometric functions and Meijer G

Traversal: all §§16.1–16.27 checked; matching headings are §16.2 and §16.17.

### §16.2: Definition and analytic properties

- **Generalized ₚFq and its formal/terminating series**, [16.2.1](https://dlmf.nist.gov/16.2.E1):
  `DLMF.Hypergeometric.genCoeff`, `genFormalSeries`, `genFiniteHG`, `genHG`
  in [GeneralizedHypergeometric/Basic](DLMF/GeneralizedHypergeometric/Basic.lean#L49).
  `GenPrincipalContinuation` specifies the principal continuation for `p=q+1`;
  `genHGLower` separately gives lower-bank values. For `p>q+1` nonterminating
  series values are not a continuation: use the Barnes constructions
  `genHasBarnesValueLog`, `genBarnesHGLog` in the same file.
- **Excess γq**, [16.2.2](https://dlmf.nist.gov/16.2.E2):
  `DLMF.Hypergeometric.genExcess` in
  [Basic](DLMF/GeneralizedHypergeometric/Basic.lean#L166).
- **Regularized generalized hypergeometric function**, [16.2.5](https://dlmf.nist.gov/16.2.E5):
  Mathlib `Complex.regularizedHGFunCoeff`, `regularizedHGFunSeries`,
  `regularizedHGFun` in
  [RegularizedHypergeometric](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean#L67)
  are native series objects. `DLMF.Hypergeometric.genRegularizedHG` in
  [Basic](DLMF/GeneralizedHypergeometric/Basic.lean#L127) additionally chooses
  the specified principal continuation when `p=q+1`; existence obligations
  are separate. Multisets encode unordered upper and lower parameter lists.

Complementary **Appell F₁,F₂,F₃,F₄** definitions occur under
[§16.13 “Appell Functions”, 16.13.1–4](https://dlmf.nist.gov/16.13):
`DLMF.Hypergeometric.appF1`, `appF2`, `appF3` in
[DefinitionsAndSeries](DLMF/GeneralizedHypergeometric/Appell/DefinitionsAndSeries.lean#L124),
and `appF4` in [AppellF4](DLMF/Hypergeometric/AppellF4.lean#L348).
The four `appF1Euler`–`appF4Euler` definitions in
[EulerIntegrals](DLMF/GeneralizedHypergeometric/Appell/EulerIntegrals.lean#L61)
are independent integral constructions; their domains differ from the double-series
domains. `appF4InfinityExpression`, `appF4InfinityBranch` in
[AppellContinuation](DLMF/GeneralizedHypergeometric/AppellContinuation.lean#L25)
give a particular continued branch. `IsAppellContinuation`, `IsAppellBranchAt`
specify general continuation data, rather than a globally single-valued Appell function.

### §16.17: Definition of Meijer G

- **Meijer G, logarithmic branches, and the three admissible contour types**,
  [16.17.1 and contour prose](https://dlmf.nist.gov/16.17.E1):
  `DLMF.Hypergeometric.MeijerGParameters`, `MeijerContourKind`,
  `MeijerGContour`, `meijerGKernelLog`, `MeijerGHasValueLog`,
  `MeijerGConvergesLog`, `meijerGLog`, and `meijerG` in
  [MeijerG](DLMF/GeneralizedHypergeometric/MeijerG.lean#L28).
  Pole separation, orientation and convergence are recorded explicitly by
  `Valid`, `Admissible`, and `meijerGContourRegion`. The principal function
  specializes the logarithmic one with `Complex.log`; a zero fallback outside
  the existence predicate is not a convergent contour value.

## Chapter 17 — q-hypergeometric and related functions

Traversal: all §§17.1–17.19 checked; no heading contains “Definition” or
“Definitions”. The following are complementary entries from
§17.2 “Calculus” and §17.4 “Basic Hypergeometric Functions”.

- **Finite, negative-integral, complex-order and infinite q-Pochhammer
  symbols**, [17.2.1–6](https://dlmf.nist.gov/17.2.E1):
  `DLMF.QSeries.qPochhammer`, `qPochhammerInf` in
  [Pochhammer](DLMF/QSeries/Pochhammer.lean#L31);
  list variants `DLMF.QHypergeometric.qPochhammerList`,
  `qPochhammerListInt`, `qPochhammerListInf`, and complex-order
  `qPochhammerOrder` in [Basic](DLMF/QHypergeometric/Basic.lean#L36).
  Infinite products and complex powers require their convergence and branch
  hypotheses; a product quotient is not automatically valid at zeros.
- **q-binomial coefficients**, [17.2.27](https://dlmf.nist.gov/17.2.E27):
  recurrence definition `DLMF.QSeries.qBinom` in
  [QBinomial](DLMF/QSeries/QBinomial.lean#L29) and integer-top extension
  `DLMF.QHypergeometric.qBinomialInt` in
  [Calculus](DLMF/QHypergeometric/Calculus.lean#L65).
- **q-derivative and iterated q-derivative**, [17.2.41–42](https://dlmf.nist.gov/17.2.E41):
  `DLMF.QSeries.qDeriv` in [QCalculus](DLMF/QSeries/QCalculus.lean#L29)
  is the raw quotient; `DLMF.QHypergeometric.qDerivExtended` and
  `qDerivIterate` in [Calculus](DLMF/QHypergeometric/Calculus.lean#L33)
  additionally supply the ordinary derivative at zero.
- **Jackson q-integrals**, [17.2.45–48](https://dlmf.nist.gov/17.2.E45):
  `DLMF.QSeries.jacksonIntegral` in [Pochhammer](DLMF/QSeries/Pochhammer.lean#L107),
  and `DLMF.QHypergeometric.jacksonBetween`, `jacksonBilateral`,
  `HasNaturalJacksonIntegral`, `HasNaturalJacksonBilateral` in
  [Calculus](DLMF/QHypergeometric/Calculus.lean#L39).
  The predicates retain convergence information separately from totalized sums.
- **Basic unilateral and bilateral hypergeometric series**,
  [17.4.1](https://dlmf.nist.gov/17.4.E1), [17.4.3](https://dlmf.nist.gov/17.4.E3):
  `DLMF.QHypergeometric.qPhi`, `qPsi`, with terms and finite partial sums in
  [Basic](DLMF/QHypergeometric/Basic.lean#L50). The exponent includes DLMF's
  `(-1)ⁿ q^(n(n-1)/2)` factor; convergence regions and exceptional q-powers
  remain hypotheses, not alternative continuation definitions.
- **Four q-Appell functions**, [17.4.5–8](https://dlmf.nist.gov/17.4.E5):
  `DLMF.QHypergeometric.qAppell1`, `qAppell2`, `qAppell3`, `qAppell4`
  in [Appell](DLMF/QHypergeometric/Appell.lean#L31), double series with
  their parameter order matching the displayed formulas.
- **Balanced/Saalschützian, k-balanced, well-poised, very-well-poised and
  nearly-poised series**, [17.4.9–13](https://dlmf.nist.gov/17.4.E9):
  `DLMF.QHypergeometric.qBalanced`, `qKBalanced`, `qWellPoised`,
  `qVeryWellPoised`, `qNearlyPoised` in
  [Basic](DLMF/QHypergeometric/Basic.lean#L110).

## Chapter 18 — Orthogonal polynomials

Traversal: all §§18.1–18.42 checked; matching headings are §18.2(i),
§18.3, §18.19, §18.25, §18.33(i), §18.34(i), §18.35(i), and the three
definition paragraphs in §18.37(i)/(ii). Tables in those sections were included.

### §18.2(i): Definition of orthogonal systems

- **Orthogonality on an interval, countable set, or general measure**,
  [18.2.1–4_5 and prose](https://dlmf.nist.gov/18.2.i):
  `DLMF.OrthogonalPolynomials.IsOrthogonalPolynomials` in
  [General](DLMF/OrthogonalPolynomials/General.lean#L35), a full infinite
  sequence of real polynomials with degree, integrability, positive norm and
  pairwise orthogonality requirements. Interval weights are converted to
  measures by `weightMeasure` in
  [ClassicalInstances](DLMF/OrthogonalPolynomials/ClassicalInstances.lean#L48).
  Counting measures with weights encode discrete sets. A finite system on
  `N+1` points, 18.2.3, is not itself an instance of this infinite-sequence
  predicate; it is represented by finite orthogonality statements.

### §18.3: Classical definitions and Table 18.3.1

All local names in the following entries are in `DLMF.OrthogonalPolynomials`.
The orthogonality domains and parameter inequalities in the table are
mathematical assumptions, not restrictions on the types of these total functions.

- **Jacobi**, [Table 18.3.1](https://dlmf.nist.gov/18.3.T1):
  `jacobiPolyP` in [Classical](DLMF/OrthogonalPolynomials/Classical.lean#L485)
  is the complex hypergeometric formula; `jacobiPolyPR`, `jacobiWeight`
  and `jacobiMeasure` in
  [ClassicalInstances](DLMF/OrthogonalPolynomials/ClassicalInstances.lean#L487)
  and [Classical](DLMF/OrthogonalPolynomials/Classical.lean#L928) supply real
  polynomial and measure objects. The continued finite coefficient formula
  handles parameters for which the raw hypergeometric quotient needs care.
  The pseudo-Jacobi/Routh–Romanovski functions mentioned at the end of §18.3
  are specializations `Pₙ^(-N-1+iν,-N-1-iν)(ix)`, without a separate local name.
- **Ultraspherical/Gegenbauer**, [Table 18.3.1](https://dlmf.nist.gov/18.3.T1):
  `ultrasphPoly` in [Classical](DLMF/OrthogonalPolynomials/Classical.lean#L704)
  and real polynomial `ultrasphPolyR` in
  [ClassicalInstances](DLMF/OrthogonalPolynomials/ClassicalInstances.lean#L864).
- **Chebyshev T and U**, [Table 18.3.1](https://dlmf.nist.gov/18.3.T1): Mathlib
  `Polynomial.Chebyshev.T`, `Polynomial.Chebyshev.U` in
  [Chebyshev/Basic](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Basic.lean).
  Shifted T-star and U-star are evaluations at `2x-1`, without separate local
  definition objects. The finite cosine nodes in [18.3.2](https://dlmf.nist.gov/18.3.E2)
  are explicit expressions, not a separately named node function.
- **Chebyshev V and W**, [Table 18.3.1](https://dlmf.nist.gov/18.3.T1):
  `chebyshevV`, `chebyshevW` in [Explicit](DLMF/OrthogonalPolynomials/Explicit.lean#L56),
  with DLMF's distinct normalizations at `x=1`.
- **Legendre and shifted Legendre**, [Table 18.3.1](https://dlmf.nist.gov/18.3.T1):
  `legendrePolyP` in [Classical](DLMF/OrthogonalPolynomials/Classical.lean#L495),
  the Jacobi specialization, and the corresponding real polynomial objects
  used in [Legendre](DLMF/OrthogonalPolynomials/Legendre.lean).
  Mathlib's `Polynomial.shiftedLegendre` in
  [ShiftedLegendre](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean)
  is an independent polynomial construction;
  `aeval_shiftedLegendre_eq_legendrePolyP` is the normalization/argument bridge.
- **Laguerre**, [Table 18.3.1](https://dlmf.nist.gov/18.3.T1):
  `laguerrePolyL` in [Classical](DLMF/OrthogonalPolynomials/Classical.lean#L207),
  continued finite-sum `laguerreExtended` in
  [Explicit](DLMF/OrthogonalPolynomials/Explicit.lean#L39),
  `laguerrePolyLR`, `laguerreWeight`, and `laguerreMeasure` in
  [ClassicalInstances](DLMF/OrthogonalPolynomials/ClassicalInstances.lean#L362).
  `laguerreExtended` remains the polynomial at negative-integral α where
  the raw M-based definition can differ by totalization.
- **Hermite H and He**, [Table 18.3.1](https://dlmf.nist.gov/18.3.T1):
  physicists' `hermitePolyH` in
  [Classical](DLMF/OrthogonalPolynomials/Classical.lean#L38) and real-coefficient
  alias `hermitePolyHR` in
  [AngularRepresentations](DLMF/OrthogonalPolynomials/Integrals/AngularRepresentations.lean#L56);
  probabilists' Mathlib `Polynomial.hermite` in
  [Hermite/Basic](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/Hermite/Basic.lean).
  The weights are `exp(-x²)` and `exp(-x²/2)` respectively; these normalizations
  should not be interchanged.

### §18.19: Hahn-class definitions

- **Hahn, Krawtchouk, Meixner and Charlier**, [Tables 18.19.1–2](https://dlmf.nist.gov/18.19.T1):
  `DLMF.OrthogonalPolynomials.hahn`, `krawtchouk`, `meixner`, `charlier`
  in [HahnAndMeixner](DLMF/OrthogonalPolynomials/Hahn/HahnAndMeixner.lean#L118),
  all defined by finite hypergeometric sums. `charlierPoly` in
  [CharlierAndConnections](DLMF/OrthogonalPolynomials/Hahn/CharlierAndConnections.lean#L273)
  is a polynomial-valued realization. `hahnWeightInt` and `charlierWeightInt`
  in [HahnRodrigues](DLMF/OrthogonalPolynomials/HahnRodrigues.lean#L28) and
  [DiscreteRodrigues](DLMF/OrthogonalPolynomials/DiscreteRodrigues.lean#L31)
  are actual discrete weight objects; remaining table weights can be written
  by their displayed factorial/binomial expressions without another wrapper.
- **Continuous Hahn and Meixner–Pollaczek**, [18.19.1–9](https://dlmf.nist.gov/18.19.E1):
  `DLMF.OrthogonalPolynomials.continuousHahn`, `meixnerPollaczek`,
  `continuousHahnWeight`, and `meixnerPollaczekWeight` in
  [HahnAndMeixner](DLMF/OrthogonalPolynomials/Hahn/HahnAndMeixner.lean#L139).
  Continuous Hahn has four independent complex parameters in the definition;
  its positive orthogonality regime sets the latter pair to conjugates of the
  first. Meixner–Pollaczek uses DLMF's angle φ and gamma weight.
- **Hahn/Wilson class and lattice-difference terminology**, [§18.19 prose](https://dlmf.nist.gov/18.19):
  no separate class structure is defined. The distinction is reflected by the
  linear or quadratic polynomial arguments of the individual families.

### §18.25: Wilson-class definitions

- **Wilson, continuous dual Hahn, Racah and dual Hahn**,
  [Table 18.25.1 and 18.25.3–15](https://dlmf.nist.gov/18.25.T1):
  `DLMF.OrthogonalPolynomials.wilson`, `continuousDualHahn`, `racah`,
  `dualHahn` in [Wilson](DLMF/OrthogonalPolynomials/Wilson.lean#L34).
  Their argument is the polynomial variable `x=y²` or
  `x=y(y+γ+δ+1)`, not y itself; the product formulas avoid choosing a square root.
  The section's gamma-ratio weights, squared norms, lattice transformations,
  and leading coefficients are explicit expressions in the local theorem
  statements, rather than additional public definition objects.

### §18.33(i): Definition on the unit circle

- **Unit-circle orthogonal/orthonormal polynomial systems**,
  [18.33.1](https://dlmf.nist.gov/18.33.E1):
  `DLMF.OrthogonalPolynomials.IsUnitCircleOP` in
  [UnitCircle](DLMF/OrthogonalPolynomials/UnitCircle.lean#L41) specifies
  **monic** orthogonal polynomials for a probability measure on the circle.
  DLMF's displayed system is orthonormal; norm rescaling is needed to obtain
  that normalization. `IsUnitCircleOP.ip` is the measure inner product.

### §18.34(i): Bessel definitions

- **Generalized Bessel yₙ(x;a), ordinary yₙ and reverse θₙ**,
  [18.34.1–3](https://dlmf.nist.gov/18.34.E1):
  `DLMF.OrthogonalPolynomials.besselPolynomial` and `reverseBesselPolynomial`
  in [Associated](DLMF/OrthogonalPolynomials/Associated.lean#L74).
  The first uses DLMF's parameter a (not the shifted convention a-2 of
  Koekoek et al.); a=2 gives ordinary y. The reversal is a finite polynomial,
  so its zero value is retained. Two-parameter `(a,b)` variants are argument
  rescalings, without separate named definitions.

### §18.35(i): Pollaczek definitions

- **Three Pollaczek types and associated type 2/type 3**,
  [18.35.0_5–2](https://dlmf.nist.gov/18.35.E0_5):
  `DLMF.OrthogonalPolynomials.pollaczek` in
  [Associated](DLMF/OrthogonalPolynomials/Associated.lean#L68), with complex
  `λ,a,b`, real shift c, and natural degree. Set c=0 for type 2 and additionally
  λ=1/2 for type 1. The degree -1 initial value is implicit in the recurrence;
  there is no negative-degree function argument.
- **Monic Pollaczek Q and angular τ**, [18.35.2_2](https://dlmf.nist.gov/18.35.E2_2),
  [18.35.3](https://dlmf.nist.gov/18.35.E3): Q is the displayed Pochhammer
  rescaling of `pollaczek`, without a separate function; τ is
  `DLMF.OrthogonalPolynomials.pollaczekTau` in
  [Associated](DLMF/OrthogonalPolynomials/Associated.lean#L1086).

### §18.37(i), (ii): Disk and triangle definitions

- **Disk polynomials**, [18.37.1](https://dlmf.nist.gov/18.37.E1),
  [equivalent characterization 18.37.3–5](https://dlmf.nist.gov/18.37.E3):
  `DLMF.OrthogonalPolynomials.diskPolynomial` in
  [Multivariate](DLMF/OrthogonalPolynomials/Multivariate.lean#L37), defined by
  the explicit polynomial in z and conjugate z from 18.37.6. The polar Jacobi
  formula and orthogonality characterization are bridges, not additional definitions.
- **Triangle polynomials**, [18.37.7](https://dlmf.nist.gov/18.37.E7):
  `DLMF.OrthogonalPolynomials.trianglePolynomial` in
  [Multivariate](DLMF/OrthogonalPolynomials/Multivariate.lean#L45), with `n ≤ m`
  and the DLMF triangle `0 < y < x < 1`. Its product formula involves `y/x`;
  the totalized boundary value is not automatically the polynomial extension.

## Chapter 19 — Elliptic integrals

Traversal: all §§19.1–19.39 checked; matching sections are §19.2 and §19.16.

### §19.2: Definitions

- **General elliptic integral**, [19.2.1–3 and prose](https://dlmf.nist.gov/19.2.i):
  no general Lean structure for the class of rational integrands on a
  cubic/quartic square-root curve. The particular functions below are defined.
- **Legendre incomplete F, E, D and Π**, [19.2.4–7](https://dlmf.nist.gov/19.2.E4):
  `DLMF.EllipticIntegrals.incEllIntFk`, `incEllIntEk`, `incEllIntDk`,
  `incEllIntPik` in [Legendre](DLMF/EllipticIntegrals/Legendre.lean#L151),
  complex segment integrals using principal square roots and a principal-value
  construction for interior Π poles. The Π argument is the characteristic
  `α²` itself, followed by modulus k. Independent real parameter-m integrals
  are `DLMF.Elliptic.Real.incEllIntFm`, `incEllIntEm` in
  [Jacobi](DLMF/Elliptic/Jacobi.lean#L33), and `incEllIntPim` in
  [ThirdKind](DLMF/Elliptic/ThirdKind.lean#L39), with `m=k²`.
  lean-codes also defines real modulus-k F, E, Π as
  `Carlson.Real.incEllIntFk`, `incEllIntEk`, `incEllIntPik` in
  [Carlson/Elliptic/Standard](../lean-codes/Carlson/Elliptic/Standard.lean#L78).
  The ordinary real Π interval integrals do not implement principal values.
- **Complete K, E, D and Π**, [19.2.8](https://dlmf.nist.gov/19.2.E8):
  `DLMF.JacobiElliptic.compEllIntKk` in
  [Definitions](DLMF/JacobiElliptic/Basic/Definitions.lean#L97) is a complex
  t-integral; `DLMF.EllipticIntegrals.compEllIntEk`, `compEllIntDk`,
  `compEllIntPik` in [Legendre](DLMF/EllipticIntegrals/Legendre.lean#L184)
  specialize the amplitude to π/2. Real parameter-m K/E are
  `DLMF.Elliptic.Real.compEllIntKm`, `compEllIntEm` in
  [Complete](DLMF/Elliptic/Complete.lean#L118), and real Π is
  `DLMF.Elliptic.Real.compEllIntPim` in [ThirdKind](DLMF/Elliptic/ThirdKind.lean#L42).
  lean-codes has independent real modulus-k `Carlson.Real.compEllIntKk`,
  `compEllIntEk` in [Standard](../lean-codes/Carlson/Elliptic/Standard.lean#L93).
- **Complementary K-prime and E-prime**, [19.2.8_1–9](https://dlmf.nist.gov/19.2.E8_1):
  `DLMF.JacobiElliptic.compEllIntKpk` is the literal complementary-modulus
  integral; `DLMF.EllipticIntegrals.cCompEllIntKk`, `cCompEllIntEk` in
  [Legendre](DLMF/EllipticIntegrals/Legendre.lean#L204) include the extra
  continuation terms on the left half-plane. These are materially different
  branch constructions, not interchangeable aliases for `K(sqrt(1-k²))`.
- **Bulirsch cel, el1, el2 and el3**, [19.2.11–16](https://dlmf.nist.gov/19.2.E11):
  `DLMF.EllipticIntegrals.bulirschCel`, `bulirschEl1`, `bulirschEl2`,
  `bulirschEl3` in [Legendre](DLMF/EllipticIntegrals/Legendre.lean#L226).
  The complementary modulus is complex; coefficients/characteristic p are real
  where typed so, and the specified singular cases use principal values.
- **Elementary degenerate RC**, [19.2.17](https://dlmf.nist.gov/19.2.E17):
  `DLMF.EllipticIntegrals.symEllIntRC` in
  [Symmetric](DLMF/EllipticIntegrals/Symmetric.lean#L134), with a Cauchy
  principal value for negative real y. `Carlson.TwoVariable.carlsonRC` in
  [QuadraticHybrid](../lean-codes/Carlson/TwoVariable/QuadraticHybrid.lean#L225)
  is an independent R-function specialization, with its own slit-domain use.

### §19.16: Symmetric-integral definitions

- **RF, RJ, RG, RD and kernel s(t)**, [19.16.1–5](https://dlmf.nist.gov/19.16.E1):
  `DLMF.EllipticIntegrals.symEllIntRF`, `symEllIntRJ`, `symEllIntRG`,
  `symEllIntRD`, `symEllIntS` in
  [Symmetric](DLMF/EllipticIntegrals/Symmetric.lean#L99).
  These are normalized integrals; RD is an alias specialization of RJ.
  RJ has an explicit principal-value branch for negative real p. Independent
  continued R-function realizations are `Carlson.carlsonRF` in
  [RF](../lean-codes/Carlson/Elliptic/RF.lean#L47) and `Carlson.carlsonRG`
  in [Standard](../lean-codes/Carlson/Elliptic/Standard.lean#L58).
- **Five-root hyperelliptic integral**, [19.16.7](https://dlmf.nist.gov/19.16.E7):
  no specifically named five-root function found; it is expressible as a
  specialization of the general R integral.
- **Multivariate R-minus-a and conjugate parameter a-prime**,
  [19.16.8–10](https://dlmf.nist.gov/19.16.E8):
  `DLMF.EllipticIntegrals.symEllIntR`, `symEllIntRConj` in
  [Symmetric](DLMF/EllipticIntegrals/Symmetric.lean#L149).
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

## Chapter 20 — Theta functions

Traversal: all §§20.1–20.16 checked; the matching section is §20.2.

### §20.2: Definitions and periodic properties

- **Four Jacobi theta functions**, [20.2.1–4](https://dlmf.nist.gov/20.2.E1):
  `DLMF.Elliptic.jacobiThetaOneTau`, `jacobiThetaTwoTau`,
  `jacobiThetaThreeTau`, `jacobiThetaFourTau` in
  [Theta/Defs](DLMF/Elliptic/Theta/Defs.lean#L27), and independent nome-series
  definitions `DLMF.Theta.jacobiThetaOneQ`, `jacobiThetaTwoQ`,
  `jacobiThetaThreeQ`, `jacobiThetaFourQ` in
  [Basic](DLMF/Theta/Basic.lean#L47). Mathlib `jacobiTheta₂` in
  [TwoVariable](.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean)
  is the native two-variable construction underlying theta-three, with
  argument `z/π`; its subscript does not mean DLMF theta-two. The nome is
  `q=exp(πiτ)`. Nome powers in theta-one/two use a principal quarter-power,
  so converting from τ must respect the selected logarithm.
- **Theta constants and derivative at zero**, [20.2(i) prose](https://dlmf.nist.gov/20.2.i):
  `DLMF.Theta.jacobiThetaTwoNullTau`, `jacobiThetaThreeNullTau`,
  `jacobiThetaFourNullTau`, `jacobiThetaTwoNullQ`, `jacobiThetaThreeNullQ`,
  `jacobiThetaFourNullQ` are abbreviations
  at z=0; `jacobiThetaOneDerivNullTau`, `jacobiThetaOneDerivNullQ` are
  derivative definitions in [Basic](DLMF/Theta/Basic.lean#L64).
- **Lattice points and half-period multiplier M**,
  [20.2.5](https://dlmf.nist.gov/20.2.E5), [20.2.10](https://dlmf.nist.gov/20.2.E10):
  `DLMF.Theta.latticePoint`, `thetaMultiplierM` in
  [Basic](DLMF/Theta/Basic.lean#L323). The fundamental parallelogram is a
  region described by its vertices, without another local region definition.

## Chapter 21 — Multidimensional theta functions

Traversal: all §§21.1–21.11 checked; the matching section is §21.2.

### §21.2: Definitions

- **Riemann theta**, [21.2.1](https://dlmf.nist.gov/21.2.E1):
  `DLMF.RiemannTheta.riemannTheta` and its summand `riemannThetaTerm` in
  [Basic](DLMF/RiemannTheta/Basic.lean#L56), with an arbitrary finite index
  type for genus. `siegelUpperHalfSpace` is the symmetric positive-imaginary-part
  matrix domain from §21.1. `riemannThetaBig` is the alternative normalization
  `Θ(φ|B)=θ(φ/(2πi)|B/(2πi))`, not an independent continuation.
- **Scaled Riemann theta**, [21.2.2](https://dlmf.nist.gov/21.2.E2):
  `DLMF.RiemannTheta.riemannThetaScaled` in
  [Basic](DLMF/RiemannTheta/Basic.lean#L81). This is an exact nonanalytic
  rescaling, not a numerical approximation, so it belongs in the inventory.
- **Theta with characteristics and half-period characteristics**,
  [21.2.5 and adjacent prose](https://dlmf.nist.gov/21.2.E5):
  `DLMF.RiemannTheta.riemannThetaChar`, `riemannThetaCharTerm`, and
  `halfPeriodCharacteristics` in [Basic](DLMF/RiemannTheta/Basic.lean#L68).
  The characteristic vectors are real; the final set restricts each entry
  to 0 or 1/2. The translated-theta formula 21.2.6 is a bridge.

## Chapter 22 — Jacobian elliptic functions

Traversal: all §§22.1–22.22 checked; matching headings are §22.2,
§22.15(i), and the “Definition” paragraphs in §22.16(i)/(iii).

### §22.2: Definitions

- **Nome, modulus, complementary modulus, K and scaled argument ζ**,
  [22.2.1–3](https://dlmf.nist.gov/22.2.E1):
  `DLMF.JacobiElliptic.jacobiNomek`, `jacobiTauk`, `jacobiComodulusk`,
  `jacobiZetak`, `compEllIntKk`, `compEllIntKpk`, and the τ-based
  `jacobiModulusTau`, `jacobiComodulusTau`, `compEllIntKTau`,
  `compEllIntKpTau`, `jacobiZetaTau` in
  [Definitions](DLMF/JacobiElliptic/Basic/Definitions.lean#L68).
  Here “Zeta” denotes the scaled argument πz/(2K), not Jacobi's zeta function.
- **All twelve Jacobi functions and Glaisher quotients**,
  [22.2.4–12](https://dlmf.nist.gov/22.2.E4):
  `DLMF.JacobiElliptic.jacobiGlaisher`, `jacobiPQTau`, `jacobiPQk`, with
  `JacobiLetter`, in [Definitions](DLMF/JacobiElliptic/Basic/Definitions.lean#L60).
  The explicit modulus-k wrappers are `jacobiSnk`, `jacobiCnk`, `jacobiDnk`,
  `jacobiSdk`, `jacobiCdk`, `jacobiSck`, `jacobiNsk`, `jacobiNck`,
  `jacobiNdk`, `jacobiDsk`, `jacobiDck`, `jacobiCsk`; each has a corresponding
  τ wrapper `jacobiSnTau`, …, `jacobiCsTau` in the same file.
  Independent real inverse-integral constructions are
  `DLMF.Elliptic.Real.jacobiSnm`, `jacobiCnm`, `jacobiDnm` in
  [Jacobi](DLMF/Elliptic/Jacobi.lean#L219), with parameter `m=k²`.
  Their amplitude definition uses a fallback when `m ≥ 1`; it is not a
  general mathematical extension to that regime.

### §22.15(i): Definitions of inverse Jacobi functions

- **Principal arcsn, arccn and arcdn**, [22.15.1–10](https://dlmf.nist.gov/22.15.E1):
  `DLMF.Elliptic.Real.jacobiArcsnm` in
  [SpecialValues](DLMF/Elliptic/SpecialValues.lean#L86),
  `DLMF.JacobiElliptic.Real.jacobiArccnm`, `jacobiArcdnm` in
  [Inverse](DLMF/JacobiElliptic/Inverse.lean#L45). They use parameter m,
  with the DLMF principal intervals and range conditions in theorems.
  The other nine inverse functions are independently defined there as
  `jacobiArccdm`, `jacobiArcsdm`, `jacobiArcndm`, `jacobiArcdcm`,
  `jacobiArcncm`, `jacobiArcscm`, `jacobiArcnsm`, `jacobiArcdsm`,
  `jacobiArccsm`. General real solution sets are theorem characterizations;
  no multivalued complex inverse object is defined.

### §22.16(i), (iii): Amplitude and zeta definitions

- **Jacobi amplitude**, [22.16.1 and continuation prose](https://dlmf.nist.gov/22.16.E1):
  `DLMF.Elliptic.Real.jacobiAmm` in
  [Jacobi](DLMF/Elliptic/Jacobi.lean#L159), the inverse order isomorphism of F
  when `m<1`. This is the unwrapped real amplitude, not principal arcsine
  of sn on the whole real line.
- **Jacobi zeta Z**, [22.16.32](https://dlmf.nist.gov/22.16.E32):
  `DLMF.JacobiElliptic.Real.jacobiZetaFunctionk`, using the independently
  defined integral `Real.jacobiEpsilonk` in
  [Related](DLMF/JacobiElliptic/Related.lean#L193).
  Epsilon is the exact integral of dn² and supplies the referenced quantity
  in the definition; it is distinct from the scaled argument called `jacobiZetak`.

## Chapter 23 — Weierstrass elliptic and modular functions

Traversal: all §§23.1–23.24 checked; matching sections are §23.2 and §23.15.

### §23.2: Definitions and periodic properties

- **Lattice and half-periods**, [§23.2(i), 23.2.1–3](https://dlmf.nist.gov/23.2.i):
  `DLMF.Weierstrass.HalfPeriods`, `HalfPeriods.ω₂`, `tau`, `nome`,
  `periodPair`, and `lattice` in
  [LatticesAndSigma](DLMF/Weierstrass/Basic/LatticesAndSigma.lean#L35).
  Mathlib `PeriodPair` and `PeriodPair.lattice` in
  [Weierstrass](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean#L60)
  store **full periods**, without the orientation requirement; the local
  conversion supplies `2ω₁,2ω₃` and retains DLMF's positive ratio orientation.
- **Weierstrass ℘**, [23.2.4](https://dlmf.nist.gov/23.2.E4): Mathlib
  `PeriodPair.weierstrassP` and `derivWeierstrassP` in
  [Weierstrass](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean#L268).
  The local `HalfPeriods.weierstrassP`, `derivWeierstrassP` are abbreviations
  through the full-period conversion. Invariant-based alternatives
  `weierstrassPInvariants`, `weierstrassZetaInvariants`, `weierstrassSigmaInvariants`
  in [EllipticFunctionsAndInvariants](DLMF/Weierstrass/Basic/EllipticFunctionsAndInvariants.lean#L961)
  choose a lattice with specified invariants, rather than a new lattice sum.
- **Weierstrass ζ and σ**, [23.2.5–6](https://dlmf.nist.gov/23.2.E5):
  `DLMF.Weierstrass.weierstrassZeta`, `weierstrassSigma` in
  [LatticesAndSigma](DLMF/Weierstrass/Basic/LatticesAndSigma.lean#L264),
  a lattice sum and product respectively; half-period methods are abbreviations.
  Totalized lattice-point values do not represent poles of ζ or ℘.
- **Elliptic function and quasi-period constants ηⱼ**,
  [§23.2(iii) prose and 23.2.12](https://dlmf.nist.gov/23.2.iii):
  η is `DLMF.Weierstrass.HalfPeriods.eta` in
  [EllipticFunctionsAndInvariants](DLMF/Weierstrass/Basic/EllipticFunctionsAndInvariants.lean#L268).
  Meromorphicity and double periodicity are expressed through their standard
  predicates; there is no separate local class called `EllipticFunction`.

### §23.15: Modular definitions

- **Modular transformation, modular function, modular form and cusp form**,
  [23.15.3–5 and prose](https://dlmf.nist.gov/23.15.i):
  `DLMF.Weierstrass.mobius`, `IsModularFunction`, `IsModularForm`,
  `IsCuspForm` in [ModularFunctions](DLMF/Weierstrass/ModularFunctions.lean#L72).
  They follow DLMF's multiplier and half-integer exponent convention with
  doubled integer weight `ℓ₂`; this is not simply an alias for Mathlib's
  integral-weight `ModularForm` and `CuspForm` structures.
- **Modular λ and Klein J**, [23.15.6–7](https://dlmf.nist.gov/23.15.E6):
  `DLMF.Weierstrass.modularLambda`, `kleinJ` in
  [ModularFunctions](DLMF/Weierstrass/ModularFunctions.lean#L113).
  J uses DLMF's normalization, so the classical j-invariant has an extra
  factor 1728. `DLMFMathlib`'s `p3wJ` in
  [P3wJSurjective](DLMFMathlib/NumberTheory/ModularForms/P3wJSurjective.lean#L33)
  is an independent Eisenstein-series quotient with that same J normalization.
- **Dedekind eta and θ₁ derivative**, [23.15.8–9](https://dlmf.nist.gov/23.15.E8):
  the derivative is `DLMF.Theta.jacobiThetaOneDerivNullTau`; Mathlib's
  `ModularForm.eta` construction in
  [DedekindEta](.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/DedekindEta.lean#L57)
  is used directly. The local identities identify the correct cube-root
  branch, rather than defining eta by a principal cube root without qualification.

## Chapter 24 — Bernoulli and Euler polynomials

Traversal: all §§24.1–24.21 checked; the matching section is §24.2, including
its tables. Exact entries instantiate the definitions; decimal approximations
are numerical and introduce no further functions.

### §24.2: Definitions and generating functions

- **Bernoulli numbers and polynomials**, [24.2.1–5](https://dlmf.nist.gov/24.2.E1):
  Mathlib `bernoulli` in
  [Bernoulli](.lake/packages/mathlib/Mathlib/NumberTheory/Bernoulli.lean#L195),
  `Polynomial.bernoulli` in
  [BernoulliPolynomials](.lake/packages/mathlib/Mathlib/NumberTheory/BernoulliPolynomials.lean),
  the real evaluation `bernoulliFun` in
  [ZetaValues](.lake/packages/mathlib/Mathlib/NumberTheory/ZetaValues.lean#L48),
  and complex-evaluation wrapper `DLMF.BernoulliEuler.bernoulliPolyB` in
  [Basic](DLMF/BernoulliEuler/Basic.lean#L52). DLMF uses `B₁=-1/2`;
  Mathlib `bernoulli'` has the other sign convention and is not its direct equivalent.
  The native formal generating function `bernoulliPowerSeries` is defined in
  [Bernoulli](.lake/packages/mathlib/Mathlib/NumberTheory/Bernoulli.lean#L266).
- **Euler numbers and polynomials**, [24.2.6–10](https://dlmf.nist.gov/24.2.E6):
  `Polynomial.euler`, `eulerNumber`, `eulerFun` in
  [EulerPolynomials](DLMFMathlib/NumberTheory/EulerPolynomials.lean#L61),
  and complex wrapper `DLMF.BernoulliEuler.eulerPolyE` in
  [Basic](DLMF/BernoulliEuler/Basic.lean#L57). The number normalization is
  `2ⁿ Eₙ(1/2)`, retaining DLMF's alternating even Euler numbers.
- **Periodic Bernoulli and antiperiodic Euler functions**,
  [24.2.11–12](https://dlmf.nist.gov/24.2.E11):
  `DLMF.BernoulliEuler.periodicBernoulliB`, `periodicEulerE` in
  [Basic](DLMF/BernoulliEuler/Basic.lean#L238), using fractional part and
  the integer-part sign for Euler. Their values at integers follow the
  half-open interval convention, especially relevant in degree one.
  The real definitions `periodicBernoulli` in
  [EulerMaclaurin](DLMFMathlib/Analysis/EulerMaclaurin.lean#L48) and
  `antiperiodicEuler` in [BooleSummation](DLMFMathlib/Analysis/BooleSummation.lean#L40)
  repeat these same expressions. Mathlib's `periodizedBernoulli` in
  [ZetaValues](.lake/packages/mathlib/Mathlib/NumberTheory/ZetaValues.lean#L274)
  is the corresponding function on `UnitAddCircle`; the local equality
  theorem makes the change of domain explicit.
- **Coefficient arrays bₙₖ and eₙₖ**, [Tables 24.2.5–6](https://dlmf.nist.gov/24.2.T5):
  coefficients of `Polynomial.bernoulli n` and `Polynomial.euler n`, via
  `Polynomial.coeff`; no separate local coefficient-array definitions.

## Chapter 25 — Zeta and related functions

Traversal: all §§25.1–25.21 checked; matching headings are §25.2
(including (i)), §25.11(i), §25.14(i), and §25.15(i).

### §25.2: Definition and expansions

- **Riemann zeta**, [25.2.1 and continuation prose](https://dlmf.nist.gov/25.2.E1):
  Mathlib `riemannZeta` in
  [RiemannZeta](.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L121),
  obtained from the continued Hurwitz theory. Its Dirichlet series is a
  theorem representation for `Re s > 1`; `LSeries (fun _ => 1)` is an independent
  generic series construction, not the continued zeta function at other s.
- **Stieltjes constants**, [25.2.4–5](https://dlmf.nist.gov/25.2.E5):
  `DLMF.Zeta.stieltjesSeq`, `stieltjesConstant` in
  [Riemann](DLMF/Zeta/Riemann.lean#L92), the exact limit with DLMF's
  `(-1)ⁿ/n!` Laurent-coefficient convention.

### §25.11(i): Hurwitz definition

- **Hurwitz ζ(s,a)**, [25.11.1](https://dlmf.nist.gov/25.11.E1):
  `DLMF.Confluent.hurwitzZetaComplex` in
  [S25bHurwitzCore](DLMF/Zeta/S25bHurwitzCore.lean#L434), a complex-a
  Euler–Maclaurin limit using principal powers. Mathlib `hurwitzZeta` in
  [HurwitzZeta](.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/HurwitzZeta.lean#L53)
  has a `UnitAddCircle` parameter; comparison with DLMF's positive real a
  requires its fundamental representative and shift terms, not mere coercion.
  The series is a bridge for `Re s > 1`; `s=1` and excluded nonpositive
  integral a require their own mathematical interpretation.

### §25.14(i): Lerch definition

- **Lerch transcendent Φ(z,s,a)**, [25.14.1](https://dlmf.nist.gov/25.14.E1):
  `DLMF.Zeta.lerchPhiSeries`, `lerchPhi`, and parameter-domain predicate
  `z25b_lerchParamOK` in [Lerch](DLMF/Zeta/Lerch.lean#L46).
  The continued function chooses an analytic extension on `ℂ \ [1,∞)`;
  on the cut it retains the totalized series, which does not encode DLMF's
  two boundary values. A separate actual integral construction
  `q25b_lerchInt` and continuation predicate `q25b_IsLerchCont` occur in
  [Q25bLerchContinuation](DLMF/Zeta/Q25bLerchContinuation.lean#L125).
  Lerch's historical K notation is an exponential-argument specialization,
  without a separate local function.
- **Referenced polylogarithm**, [25.14.3](https://dlmf.nist.gov/25.14.E3),
  complementing [definition 25.12.10](https://dlmf.nist.gov/25.12.E10):
  `DLMF.Zeta.polylogSeriesC`, `polylog` in
  [Polylog](DLMF/Zeta/Polylog.lean#L86), and natural-order series
  `DLMF.Polylog.polylogSeries` in [Basic](DLMF/Polylog/Basic.lean#L34).
  The complex-order continuation has the same cut/fallback distinction as
  Lerch Φ; the natural-order series is not its global continuation.

### §25.15(i): Dirichlet L definitions

- **Dirichlet L(s,χ)**, [25.15.1](https://dlmf.nist.gov/25.15.E1): Mathlib
  `DirichletCharacter.LFunction` in
  [DirichletContinuation](.lake/packages/mathlib/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean#L60)
  is continued; `LSeries` applied to χ is the distinct native Dirichlet-series
  construction. Principal and nonprincipal characters have different pole behavior.
- **Gauss sum G(χ)**, [25.15.6](https://dlmf.nist.gov/25.15.E6):
  `DLMF.NumberTheory.gaussSumDLMF χ 1` in
  [Characters](DLMF/NumberTheory/Characters.lean#L858), and Mathlib `gaussSum`
  in [GaussSum](.lake/packages/mathlib/Mathlib/NumberTheory/GaussSum.lean).
  The latter takes multiplicative and additive characters explicitly; the
  local wrapper fixes DLMF's positive exponential convention.

## Chapter 26 — Combinatorial analysis

Traversal: all §§26.1–26.22 checked; matching headings are §26.2,
§26.3(i), §26.4(i), §26.5(i), §26.6(i), §26.7(i), §26.8(i), §26.9(i),
§26.10(i), §26.12(i), and §26.14(i). Tables were checked as instances of
the definitions; displayed examples do not introduce new families.

### §26.2: Basic definitions

- **Permutation and cycles**, [§26.2 prose](https://dlmf.nist.gov/26.2): Mathlib
  `Equiv.Perm`, `Equiv.Perm.cycleFactorsFinset` and cycle decomposition in
  [Cycle/Factors](.lake/packages/mathlib/Mathlib/GroupTheory/Perm/Cycle/Factors.lean).
  Mathlib permits an empty underlying type, while the opening DLMF prose says
  nonempty; the empty permutation is needed by later DLMF conventions.
- **Planar and k-dimensional lattice paths**, [§26.2 prose](https://dlmf.nist.gov/26.2):
  `DLMF.Combinatorics.stepLists`, `latticePaths`, `unitSteps`,
  `latticePathsFin` in [Basic](DLMF/Combinatorics/Basic.lean#L60), using
  finite step lists, with `StaysWeaklyAboveDiagonal` for the ballot restriction.
- **Set partitions and integer partitions**, [§26.2 prose](https://dlmf.nist.gov/26.2):
  Mathlib `Finpartition` in
  [Finpartition](.lake/packages/mathlib/Mathlib/Order/Partition/Finpartition.lean)
  represents finite-set partitions, and `Nat.Partition` in
  [Partition/Basic](.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/Partition/Basic.lean)
  represents integer partitions as multisets of positive parts.
- **Partition number p(n)**, [§26.2 prose](https://dlmf.nist.gov/26.2):
  `DLMF.Partitions.partitionFunction` in [Partitions](DLMF/Partitions.lean#L35)
  abbreviates the cardinality of `Nat.Partition n`.

### §§26.3(i), 26.4(i): Binomial and multinomial definitions

- **Binomial coefficient**, [26.3.1–2 and counting prose](https://dlmf.nist.gov/26.3.E1):
  Mathlib `Nat.choose`; `Finset.powersetCard` is the finite set of choices.
  Both include the zero convention when the lower index exceeds the upper.
  The local lattice-path interpretation is a theorem about `latticePaths`.
- **Multinomial coefficient**, [26.4.1–2](https://dlmf.nist.gov/26.4.E2):
  Mathlib `Nat.multinomial` in
  [Multinomial](.lake/packages/mathlib/Mathlib/Data/Nat/Choose/Multinomial.lean),
  and `Multiset.multinomial` when the multiplicities are stored as a multiset.
  `DLMF.Combinatorics.multisetPermutations` in
  [MultisetPermutations](DLMF/Combinatorics/MultisetPermutations.lean#L38)
  is the independently defined finite set of words with prescribed multiplicities.
- **Multiplicity partition λ and counts M₁,M₂,M₃**, [26.4.3–8](https://dlmf.nist.gov/26.4.E3):
  `Nat.Partition.parts` encodes λ; M₁ is `Multiset.multinomial` of its parts,
  M₂ is the cardinality of permutations of its cycle type, and M₃ is the
  corresponding set-partition count (`Multiset.bell`). These have upstream
  pointers in [MathlibCoverage](DLMF/Combinatorics/MathlibCoverage.lean#L88);
  no separate local `M1`, `M2`, or `M3` definitions are introduced.

### §§26.5(i)–26.8(i): Counting sequences

- **Catalan numbers**, [26.5.1](https://dlmf.nist.gov/26.5.E1): Mathlib `catalan`
  in [Catalan/Basic](.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/Catalan/Basic.lean).
  `DyckWord` in
  [DyckWord](.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/DyckWord.lean)
  gives an independent combinatorial object whose cardinality is
  the Catalan number; this is a theorem bridge, not a second scalar definition.
- **Delannoy and Motzkin numbers**, [26.6.1–2](https://dlmf.nist.gov/26.6.E1):
  `DLMF.Combinatorics.delannoy`, `motzkin` in
  [LatticePaths](DLMF/Combinatorics/LatticePaths.lean#L44), defined by recurrences;
  the path counts and displayed finite sums are theorem characterizations.
- **Narayana numbers**, [26.6.3](https://dlmf.nist.gov/26.6.E3):
  `DLMF.Combinatorics.narayana` in
  [LatticePaths](DLMF/Combinatorics/LatticePaths.lean#L92), with zero at k=0
  and exact natural division for the binomial formula when n>0. There is a
  boundary convention gap: [DLMF Table 26.6.3](https://dlmf.nist.gov/26.6.T3)
  has N(0,0)=1 for the empty path,
  whereas this definition gives zero. The existing path-count theorem assumes n≥1.
- **Large Schröder numbers**, [26.6.4](https://dlmf.nist.gov/26.6.E4): Mathlib
  `Nat.largeSchroder` in
  [Schroder](.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/Schroder.lean).
- **Bell numbers**, [26.7.1–4 and partition prose](https://dlmf.nist.gov/26.7.i):
  Mathlib `Nat.bell` in [Bell](.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/Bell.lean).
- **Signed first-kind and second-kind Stirling numbers**,
  [§26.8(i), 26.8.1–6](https://dlmf.nist.gov/26.8.i): Mathlib
  `Nat.stirlingFirst` is **unsigned**, and `Nat.stirlingSecond` has DLMF's
  second-kind convention, in
  [Stirling](.lake/packages/mathlib/Mathlib/Combinatorics/Enumerative/Stirling.lean).
  The signed DLMF first kind is
  `DLMF.Combinatorics.signedStirlingFirst` in
  [DefinitionsAndSeries](DLMF/Combinatorics/Stirling/DefinitionsAndSeries.lean#L42).

### §§26.9(i), 26.10(i): Restricted-partition definitions

- **At most k parts, and boxed restrictions**,
  [§26.9(i), 26.9.1](https://dlmf.nist.gov/26.9.i):
  `DLMF.Combinatorics.partitionCountAtMostParts`, `partitionCountBoxed`
  in [RestrictedPartitions](DLMF/Combinatorics/RestrictedPartitions.lean#L51).
  The Ferrers diagram and conjugate partition are realized through Mathlib's
  Young-diagram/partition correspondence, not a separately drawn graph object.
- **Distinct, bounded distinct, odd, difference-k and Schur restrictions**,
  [§26.10(i) prose](https://dlmf.nist.gov/26.10.i):
  `DLMF.Combinatorics.partitionCountDistinct`, `partitionCountAtMostDistinct`,
  `partitionCountOdd`, `PartsDifferAtLeast`, `partitionCountDiff`,
  `SchurCondition`, `partitionCountSchur` in
  [RestrictedProducts](DLMF/Combinatorics/PartitionIdentities/RestrictedProducts.lean#L38).
  `Nat.Partition.distincts` and `odds` are the upstream finite sets underlying
  the first and third counts.
- **Parts drawn from S, residue set Aⱼₖ, T={2,3,…}, and combined restrictions**,
  [§26.10(i) prose](https://dlmf.nist.gov/26.10.i):
  `DLMF.Combinatorics.partitionCountIn`, `residueSetPM`, `setGeTwo`,
  `partitionCountDiffTwoNoOne`, and `partitionCountAtMostDistinctBoxed` in
  [RestrictedProducts](DLMF/Combinatorics/PartitionIdentities/RestrictedProducts.lean#L83).

### §26.12(i): Plane-partition definitions

- **Plane partition, box B(r,s,t), and pp(n)**,
  [§26.12(i) prose, 26.12.1–4](https://dlmf.nist.gov/26.12.i):
  `DLMF.Combinatorics.IsPlanePartition`, `planeBox`, `planePartitionsIn`,
  `planePartitionCount` in
  [BoxFormula](DLMF/Combinatorics/PlanePartitions/BoxFormula.lean#L31).
  The public construction is a finite down-closed set of positive lattice
  triples. The independent array predicate `s26b_IsPPArray` and conversions
  `s26b_toArr`, `s26b_ofArr` in the same file realize the decreasing-array definition.
- **Symmetric, cyclically symmetric and totally symmetric plane partitions**,
  [prose before 26.12.5–8](https://dlmf.nist.gov/26.12.E5):
  `DLMF.Combinatorics.IsSymmetricPP`, `IsCyclicallySymmetricPP`,
  `IsTotallySymmetricPP` in
  [BoxFormula](DLMF/Combinatorics/PlanePartitions/BoxFormula.lean#L935).
- **Complement, self-complementary and transpose-complement conditions**,
  [prose before 26.12.9–17](https://dlmf.nist.gov/26.12.E9):
  `DLMF.Combinatorics.planeComplement`, `planeTranspose` in
  [BoxFormula](DLMF/Combinatorics/PlanePartitions/BoxFormula.lean#L948);
  the self-complementary and combined symmetry classes are equations involving
  these operations and the preceding predicates, without new named predicates.
- **Strict shifted and descending plane partitions**,
  [prose around 26.12.18–19](https://dlmf.nist.gov/26.12.E18):
  `DLMF.Combinatorics.IsStrictShiftedPP`, `IsDescendingPP`, and
  `DescendingPPIn` in
  [BoxFormula](DLMF/Combinatorics/PlanePartitions/BoxFormula.lean#L1094),
  using finite lists of rows rather than the unshifted triple-set representation.

### §26.14(i): Permutation statistics

- **Inversion number, descents, major/greater index, Eulerian number,
  excedances and weak excedances**, [26.14.1–2 and prose](https://dlmf.nist.gov/26.14.i):
  `DLMF.Combinatorics.inversionNumber`, `wordDescentSet`, `descentNumber`,
  `majorIndex`, `eulerianNumber`, `excedanceNumber`, `weakExcedanceNumber`
  in [CyclesAndExcedances](DLMF/Combinatorics/Permutations/CyclesAndExcedances.lean#L213).
  `wordInversions` and `wordMajorIndex` are the independent word-level
  definitions underlying the permutation wrappers. `Fin n` positions are
  zero-based internally; major-index summands add one to match DLMF.

## Chapter 27 — Functions of number theory

Traversal: all §§27.1–27.22 checked; the matching heading is §27.2(i).

### §27.2(i): Definitions

- **Prime factorization, ν(n), ordered primes pₙ and prime-counting π(x)**,
  [27.2.1–4](https://dlmf.nist.gov/27.2.E1): Mathlib `Nat.factorization`,
  `ArithmeticFunction.cardDistinctFactors` (notation ω), `Nat.primeCounting`,
  respectively defined in
  [Factorization/Defs](.lake/packages/mathlib/Mathlib/Data/Nat/Factorization/Defs.lean),
  [ArithmeticFunction/Misc](.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Misc.lean#L324),
  [PrimeCounting](.lake/packages/mathlib/Mathlib/NumberTheory/PrimeCounting.lean);
  and `DLMF.NumberTheory.nthPrime`, `primePi` in
  [Functions](DLMF/NumberTheory/Functions.lean#L61).
  DLMF prime indices start at 1; the local index-zero value is a fallback.
  `primePi` uses the floor of a real argument, whereas the upstream counting
  function takes a natural number.
- **Unit arithmetic function**, [27.2.5](https://dlmf.nist.gov/27.2.E5):
  the identity `1 : ArithmeticFunction R` in
  [Defs](.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean),
  with value one at n=1 and zero otherwise. DLMF considers positive n.
- **Totient power sums and Euler totient**, [27.2.6–7](https://dlmf.nist.gov/27.2.E6):
  `DLMF.NumberTheory.totientPowerSum` in
  [Functions](DLMF/NumberTheory/Functions.lean#L138), and Mathlib `Nat.totient`
  in [Totient](.lake/packages/mathlib/Mathlib/Data/Nat/Totient.lean).
- **Primitive root modulo n and reduced residue system**,
  [prose after 27.2.8](https://dlmf.nist.gov/27.2.i):
  `DLMF.NumberTheory.IsPrimitiveRootMod` in
  [Functions](DLMF/NumberTheory/Functions.lean#L163), using coprimality and
  `orderOf` in `ZMod n`. A reduced residue system is the corresponding
  pairwise incongruent list of units, without another local type.
- **Divisor d and ordered-factor dₖ**, [27.2.9](https://dlmf.nist.gov/27.2.E9):
  Mathlib `ArithmeticFunction.sigma 0` and
  `DLMF.NumberTheory.divisorCountK` in
  [Functions](DLMF/NumberTheory/Functions.lean#L198).
- **Divisor power sum σα**, [27.2.10](https://dlmf.nist.gov/27.2.E10):
  Mathlib `ArithmeticFunction.sigma` in
  [ArithmeticFunction/Misc](.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Misc.lean#L143)
  for natural exponents, and complex-exponent
  `DLMF.NumberTheory.sigmaC`, with `powC`, in
  [Functions](DLMF/NumberTheory/Functions.lean#L214).
- **Jordan Jₖ**, [27.2.11](https://dlmf.nist.gov/27.2.E11):
  `DLMF.NumberTheory.jordanTotient` in
  [Functions](DLMF/NumberTheory/Functions.lean#L260), an actual finite tuple count.
- **Möbius μ, Liouville λ and von Mangoldt Λ**, [27.2.12–14](https://dlmf.nist.gov/27.2.E12):
  Mathlib `ArithmeticFunction.moebius`, `liouville`, `vonMangoldt` in
  [Moebius](.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean),
  [Liouville](.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/Liouville.lean),
  [VonMangoldt](.lake/packages/mathlib/Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean).

## Chapter 28 — Mathieu functions and Hill's equation

Traversal: all §§28.1–28.36 checked; matching headings are §§28.2,
28.4(i), 28.5(i), 28.12, 28.20 and 28.29.

Names in this chapter are in `DLMF.Mathieu`.

### §28.2: Definitions and basic properties

- **Mathieu equation and normalized fundamental solutions wᵢ, wᵢᵢ**,
  [28.2.1 and 28.2.5](https://dlmf.nist.gov/28.2.E1):
  `IsMathieuSolution`, `mathieuWI`, `mathieuWII` in
  [Basic](DLMF/Mathieu/Basic.lean#L93). The functions are chosen from entire
  initial-value solutions, with zero fallback if existence fails; existence
  is proved by `exists_isMathieuSolution` in that file. The algebraic
  coordinate forms 28.2.2–3 are equation transformations, not separately
  defined functions.
- **Floquet solution, characteristic exponent and monodromy matrix**,
  [28.2.14–16](https://dlmf.nist.gov/28.2.E14): `IsFloquetSolution`,
  `IsMathieuCharExp`, `mathieuMonodromy` in
  [Basic](DLMF/Mathieu/Basic.lean#L220). The exponent predicate permits the
  full ambiguity ±ν+2n. DLMF's principal exponent, specified in the prose
  following 28.2.16 using the inverse cosine, has no separate selected Lean
  object. Bilateral-series coefficients are recorded under §28.12 below.
- **Characteristic values aₙ(q), bₙ(q)**,
  [Table 28.2.1 and 28.2.23–24](https://dlmf.nist.gov/28.2.T1):
  `mathieuSpecA`, `mathieuSpecB`, `mathieuA`, `mathieuB`, with the ordering
  helper `nthLeast`, in [Basic](DLMF/Mathieu/Basic.lean#L283).
  These take real q; the complex-q continuation discussed by DLMF is not a
  second defined a/b family. The spectra are boundary-value sets and their
  selected values use the parity-dependent indices n/2 and (n−1)/2;
  `mathieuB 0` is a fallback. Their nonempty ordered characterization is
  proved by `mathieuSpecA_exists` and `mathieuSpecB_exists` in the same file.
- **Periodic Mathieu functions ceₙ, seₙ**,
  [Table 28.2.2 and 28.2.29–30](https://dlmf.nist.gov/28.2.T2):
  `mathieuCe`, `mathieuSe`, with `mathieuCeZero`, `mathieuSeDerivZero`, in
  [Basic](DLMF/Mathieu/Basic.lean#L505). These are normalized multiples of
  wᵢ and wᵢᵢ for real q and complex z, using a positive square root of the
  squared norm integral. They are distinct from the noninteger-order
  symmetrizations below.

### §28.4(i): Fourier series

- **Fourier coefficients Aₘⁿ(q), Bₘⁿ(q)**,
  [28.4.1–4](https://dlmf.nist.gov/28.4.E1): `mathieuFourierA`,
  `mathieuFourierB` in [Basic](DLMF/Mathieu/Basic.lean#L602), defined by
  integrals of ceₙ and seₙ. The m=0 cosine coefficient has the additional
  factor 1/2; the same functions handle all four parity families.

### §28.5(i): Definitions

- **Second solutions feₙ, geₙ, periodic parts fₙ, gₙ and factors Cₙ, Sₙ**,
  [28.5.1–7](https://dlmf.nist.gov/28.5.E1): `mathieuFe`, `mathieuGe`,
  `mathieuFeF`, `mathieuGeG`, `mathieuFeC`, `mathieuGeS` in
  [Basic](DLMF/Mathieu/Basic.lean#L561). The construction also exposes
  `mathieuFeMu`, `mathieuFeU`, `mathieuGeMu`, `mathieuGeU`,
  `mathieuFeDerivZero`, `mathieuGeZero` in
  [Basic](DLMF/Mathieu/Basic.lean#L533). These use real q and normalized
  fundamental solutions. fe₀(z,0)=z is explicit; dividing by a vanishing
  Cₙ or Sₙ in the periodic-part definitions is totalized and does not define
  the limiting periodic parts at those exceptional parameters.

### §28.12: Definitions and basic properties

- **Noninteger characteristic value λν(q) and normal parameter values**,
  [§28.12(i), including 28.12.1–3](https://dlmf.nist.gov/28.12.i):
  `IsMathieuLambdaPath`, `MathieuNormalSegment`, `mathieuLambdaData`,
  `mathieuLambda`, `mathieuLambdaInt` in
  [Noninteger/Defs](DLMF/Mathieu/Noninteger/Defs.lean#L80).
  The selected analytic continuation follows the straight segment from 0
  to q and requires a unique endpoint, starting at ν². This is a particular
  path/domain implementation of DLMF's continuation, not a globally
  single-valued continuation across exceptional points. Integer ν is
  handled through a/b only for real q, with a zero fallback otherwise.
  The existence statement for real noninteger ν and real q,
  `mathieuNormalSegment_real`, remains admitted in
  [Properties](DLMF/Mathieu/Noninteger/Properties.lean#L253).
- **Floquet eigenfunction meν and coefficients c₂ₙν**,
  [28.12.4–5 and 28.12.11](https://dlmf.nist.gov/28.12.E4):
  `mathieuMe`, `mathieuMeCoeff`, `mathieuMeInt` in
  [Noninteger/Defs](DLMF/Mathieu/Noninteger/Defs.lean#L113).
  Noninteger functions use the chosen bilateral Fourier series with c₀(0)=1;
  integer orders use the separately specified √2 ceₙ or −√2 i seₙ
  normalization. Their noninteger characterization has the continuation
  qualification above.
- **Noninteger ceν, seν**, [28.12.12–13](https://dlmf.nist.gov/28.12.E12):
  `mathieuCeNu`, `mathieuSeNu` in
  [Noninteger/Defs](DLMF/Mathieu/Noninteger/Defs.lean#L154), the even and odd
  symmetrizations of meν. These are actual additional objects, rather than
  aliases for the integer-order `mathieuCe` and `mathieuSe` families.

### §28.20: Definitions and basic properties

- **Modified Mathieu equation and rotated angular functions**,
  [28.20.1–7](https://dlmf.nist.gov/28.20.E1): `IsModMathieuSolution`,
  `modMathieuCe`, `modMathieuSe`, `modMathieuMe`, `modMathieuFe`,
  `modMathieuGe` in [Modified/Defs](DLMF/Mathieu/Modified/Defs.lean#L69).
  Their factors of i and argument rotations follow the separate DLMF
  conventions for Ce, Se, Me, Fe and Ge.
- **Parameter h and solutions Mν⁽ʲ⁾, j=1,…,4**,
  [28.20.8–14](https://dlmf.nist.gov/28.20.E8): `modMathieuM`, with
  `ModMathieuAdmissible` and `modMathieuIndex`, in
  [Modified/Defs](DLMF/Mathieu/Modified/Defs.lean#L169).
  Lean takes h as an argument and uses q=h², rather than selecting h from q.
  Its definition is the Bessel cross-product series of 28.24.1; the large-z
  normalizations in this definition section are characterization theorems.
  Integer-order coefficients inherit the real-q restriction above.
- **Radial Mathieu Mcₙ⁽ʲ⁾, Msₙ⁽ʲ⁾ and modified Ieₙ, Ioₙ, Keₙ, Koₙ**,
  [28.20.15–20](https://dlmf.nist.gov/28.20.E15): `radialMathieuMc`,
  `radialMathieuMs`, `modMathieuIe`, `modMathieuIo`, `modMathieuKe`,
  `modMathieuKo` in [Modified/Defs](DLMF/Mathieu/Modified/Defs.lean#L200).
  These are wrappers with the stated index, h→ih rotation and phase factors.

### §28.29: Definitions and basic properties

- **Hill equation, periodic potential and normalized fundamental solutions**,
  [28.29.1–6](https://dlmf.nist.gov/28.29.E1): `IsHillSolution`,
  `IsHillPotential`, `hillWI`, `hillWII` in
  [Hill/Defs](DLMF/Mathieu/Hill/Defs.lean#L89). The potential predicate
  requires continuity, period π and mean zero; it does not require π to be
  the least period. Solutions have real independent variable and complex
  values, selected from initial-value solutions; `hill_exists_solution` is
  proved in [Floquet](DLMF/Mathieu/Hill/Floquet.lean#L75).
- **Hill Floquet solution, monodromy and discriminant Δ**,
  [28.29.7–15](https://dlmf.nist.gov/28.29.E7):
  `IsHillFloquetSolution`, `hillMonodromy`, `hillDiscriminant` in
  [Hill/Defs](DLMF/Mathieu/Hill/Defs.lean#L125).
- **Periodic and antiperiodic eigenvalues λₙ, μₙ and merged sequence λ̂ₙ**,
  [28.29.16–18](https://dlmf.nist.gov/28.29.E16):
  `hillPeriodicEigenvalue`, `hillAntiperiodicEigenvalue`, `hillEigenvalueHat`,
  with `hillMultiplierSolutions` and `hillEigenCount`, in
  [Hill/Defs](DLMF/Mathieu/Hill/Defs.lean#L171). Their infimum construction
  counts eigenspace dimensions, hence retains DLMF's repeated eigenvalues;
  μ₀ is a fallback outside DLMF's indexing.
- **Mean square N**, [28.29.19](https://dlmf.nist.gov/28.29.E19):
  `hillMeanSquare` in [Hill/Defs](DLMF/Mathieu/Hill/Defs.lean#L227).

## Chapter 29 — Lamé functions

Traversal: all §§29.1–29.22 checked; matching headings are §§29.3 and 29.12.
Names below are in `DLMF.Lame`; the prefix `Real` is nested in that namespace.

### §29.3: Definitions and basic properties

- **Four Lamé spectra aν²ᵐ, aν²ᵐ⁺¹, bν²ᵐ⁺¹, bν²ᵐ⁺²**,
  [§29.3(i) and Table 29.3.1](https://dlmf.nist.gov/29.3.i):
  `Real.lameSpectrum`, `Real.IsNthLameEigenvalue`, `Real.lameEigenvalue`,
  `Real.lameAk`, `Real.lameBk`, with `Real.LameBoundary`,
  `Real.IsLameSolution`, `Real.IsLameEigenfunction`, in
  [Basic](DLMF/Lame/Basic.lean#L130). Boolean boundary types distinguish
  vanishing values and derivatives. Lean takes the modulus k, even where
  DLMF writes k². The chosen ordered eigenvalues have a proved
  characterization `Real.lameEigenvalue_spec` for ν≥−1/2 and 0<k<1 in
  [Eigenvalues](DLMF/Lame/Eigenvalues.lean#L101).
- **Normalized Lamé functions Ecν, Esν**,
  [Table 29.3.2 and 29.3.18](https://dlmf.nist.gov/29.3.T2):
  `Real.IsNormalizedLameEigenfunction`, `Real.lameEigenfunction`,
  `Real.lameEck`, `Real.lameEsk` in [Basic](DLMF/Lame/Basic.lean#L202).
  These use the weighted dn integral and endpoint sign rules.
  `Real.lameEigenfunction_spec` proves existence and uniqueness on the same
  real parameter domain in [Eigenvalues](DLMF/Lame/Eigenvalues.lean#L163).
- **H, recurrence coefficients and continued-fraction quantities**,
  [29.3.9–17](https://dlmf.nist.gov/29.3.E9): the shifted eigenvalue H is
  the displayed arithmetic expression; the four recurrence families are
  encoded by `LameRecurrence`, `LameRecurrence.alpha`, `LameRecurrence.beta`,
  `LameRecurrence.gamma`, `LameRecurrence.Satisfies`, `lameCFLeft`, `lameCFRight` in
  [Basic](DLMF/Lame/Basic.lean#L235). These are coefficient and recurrence
  objects, rather than independent definitions of Ec or Es.

### §29.12: Definitions

- **Eight families of Lamé polynomials**,
  [29.12.1–8 and Table 29.12.1](https://dlmf.nist.gov/29.12.E1):
  `LamePolyType`, `lamePolyEk`, and its wrappers `lameUEk`, `lameSEk`,
  `lameCEk`, `lameDEk`, `lameSCEk`, `lameSDEk`, `lameCDEk`, `lameSCDEk`
  in [Polynomials/Defs](DLMF/Lame/Polynomials/Defs.lean#L52).
  These are finite Chebyshev expansions with sn/cn/dn prefactors, not
  choices from the preceding eigenfunction family. `lamePolyH` and
  `lamePolyCoeff` use the finite matrix `lameMatrix`, its sorted
  characteristic-polynomial roots `lameMatrixEigenvalue`, and recurrence
  eigenvectors `lameRecVec`; `LamePolyType.order`, `LamePolyType.signForm`,
  `LamePolyType.normForm`, `LamePolyType.prefactor`, `LamePolyType.basis`
  encode the order, sign, normalization and basis conventions.
- **Algebraic polynomial form and ordered zeros ξ₁,…,ξₙ**,
  [29.12.9–10](https://dlmf.nist.gov/29.12.E9): the algebraic form is a
  bridge theorem `lamePolyEk_algebraic_form` in
  [Polynomials/Series](DLMF/Lame/Polynomials/Series.lean#L633), not a second
  selected Lamé polynomial. The zeros are quantified tuples in that theorem
  family, rather than a defined root-list object.
- **Zero-maximization function g and region R**,
  [29.12.11–12](https://dlmf.nist.gov/29.12.E11): explicit local expressions
  in `lamePolyEk_zeros_maximize` in
  [Polynomials/Series](DLMF/Lame/Polynomials/Series.lean#L649), with no
  separately named global definitions.

## Chapter 30 — Spheroidal wave functions

Traversal: all §§30.1–30.18 checked; matching headings are §§30.3(i),
30.4(i) and 30.11(i). Names below are in `DLMF.Spheroidal`.

### §30.3(i): Eigenvalue definition

- **Eigenvalues λₙᵐ(γ²)**, [§30.3(i)](https://dlmf.nist.gov/30.3.i):
  `spheroidalSpectrum`, `spheroidalEigenvalue`, with
  `IsSpheroidalFactor`, in [Basic](DLMF/Spheroidal/Basic.lean#L156).
  Lean takes γ² as a real argument, allowing prolate and oblate cases.
  The choice uses the number n−m of smaller spectral values, with a zero
  fallback; `exists_spheroidalEigenvalue` and `spheroidalEigenvalue_spec`
  prove the characterization when m≤n in
  [Existence](DLMF/Spheroidal/Existence.lean#L64).

### §30.4(i): Angular function definition

- **Angular spheroidal function of the first kind Psₙᵐ**,
  [§30.4(i) and 30.4.1](https://dlmf.nist.gov/30.4.E1):
  `IsSpheroidalPsFactor`, `spheroidalPsFactor`, `spheroidalPs`,
  `spheroidalPsC` in [Basic](DLMF/Spheroidal/Basic.lean#L184).
  The selected analytic factor has the DLMF integral normalization and
  parity-dependent sign at zero. `spheroidalPs` is real on (−1,1);
  `spheroidalPsC` is the complex cut-plane version with explicit principal
  powers of z−1 and z+1. The factor's existence and uniqueness are proved
  by `existsUnique_isSpheroidalPsFactor` in
  [Existence](DLMF/Spheroidal/Existence.lean#L89).

### §30.11(i): Radial function definition

- **Cylinder choices Cν⁽ʲ⁾ and spherical functions ψₖ⁽ʲ⁾**,
  [30.11.1–2](https://dlmf.nist.gov/30.11.E1): `spheroidalCylinder`,
  `spheroidalPsi` in [Basic](DLMF/Spheroidal/Basic.lean#L392), dispatching
  to J, Y and the two Hankel functions. ψ⁽¹⁾ uses the entire spherical-J
  construction; ψ⁽²⁾, ψ⁽³⁾, ψ⁽⁴⁾ use the explicit square-root factors and
  inherit their branch and zero restrictions.
- **Radial spheroidal functions Sₙᵐ⁽ʲ⁾ and normalization Aₙ±ᵐ**,
  [30.11.3–4](https://dlmf.nist.gov/30.11.E3): `spheroidalRadial`,
  `spheroidalA`, `spheroidalANeg`, with `spheroidalCoeffMain`,
  `spheroidalCoeff`, `spheroidalCoeffNeg`, in
  [FerrersDefs](DLMF/Spheroidal/FerrersDefs.lean#L68).
  This is an actual bilateral spherical-Bessel series, using the angular
  expansion coefficients. γ is complex, but the implementation uses
  `(γ ^ 2).re` for coefficients, so the intended γ² must be real.

## Chapter 31 — Heun functions

Traversal: all §§31.1–31.18 checked; matching headings are §§31.14(i)
and 31.15(i). Fundamental Heun objects under other headings are included
explicitly as complementary entries. Names below are in `DLMF.Heun`.

### Complementary §§31.2–31.3, 31.12: Heun equations and local functions

- **General Heun equation and normalized local solution Hℓ**,
  [31.2.1 and 31.3.1](https://dlmf.nist.gov/31.3.E1): `heunEps`,
  `heunCoeffP`, `heunCoeffR`, `IsHeunSolOn`, `heunODECoeff`,
  `heunLocalCoeff`, `heunLocalRadius`, `heunLocal` in
  [Basic](DLMF/Heun/Basic.lean#L68). The last is the native power series
  around zero, with the coefficient of degree zero normalized to one.
  `IsHeunFunctionOn`, `IsHeunEigenvalue01`, `heunFunction01` in
  [Basic](DLMF/Heun/Basic.lean#L162) describe solutions analytic at two
  finite singularities and choose a continuation on a specified disk;
  they do not select a global branch at all singularities or at infinity.
  The chosen disk continuation still depends on admitted
  `IsHeunEigenvalue01.analyticOn_ball` in
  [HeunFunctions](DLMF/Heun/HeunFunctions.lean#L54).
  `heunPoly` in [Basic](DLMF/Heun/Basic.lean#L216) is a finite polynomial
  with q supplied as a parameter, not a separately selected eigenvalue.
- **Confluent, doubly confluent, biconfluent and triconfluent equations**,
  [31.12.1–4](https://dlmf.nist.gov/31.12.E1): `IsConfluentHeunSolOn`,
  `IsDoublyConfluentHeunSolOn`, `IsBiconfluentHeunSolOn`,
  `IsTriconfluentHeunSolOn` in [Basic](DLMF/Heun/Basic.lean#L350).
  These are solution predicates; no additional globally normalized
  confluent Heun function is selected there.

### §31.14(i): General Fuchsian equation definition

- **Fuchsian equation, exponents and normal form**,
  [31.14.1–5](https://dlmf.nist.gov/31.14.E1): `fuchsianCoeffP`,
  `fuchsianCoeffR`, `IsFuchsianSolOn`, `fuchsianNormalQ`,
  `fuchsianNormalGamma`, `fuchsianNormalCoeff` in
  [Basic](DLMF/Heun/Basic.lean#L395). The singular points and coefficients
  are finite indexed families; α and β are constrained roots of the
  displayed quadratic, rather than globally chosen exponent definitions.

### §31.15(i): Stieltjes-polynomial definition

- **Stieltjes and Van Vleck polynomials**,
  [31.15.1](https://dlmf.nist.gov/31.15.E1): `fuchsianPi`,
  `fuchsianGammaPoly`, `IsStieltjesEquation`, `IsVanVleckStieltjes` in
  [Basic](DLMF/Heun/Basic.lean#L424), using the cleared polynomial
  differential equation and degree conditions.
  A separately selected monic Stieltjes polynomial `stieltjesPoly`,
  characterized by `IsStieltjesOfIndex` and prescribed numbers of roots
  between real singularities, is in
  [Basic](DLMF/Heun/Basic.lean#L455). Its intended existence and uniqueness
  for increasing real singularities and positive weights still rely on
  admitted `existsUnique_stieltjesOfIndex` in
  [Fuchsian](DLMF/Heun/Fuchsian.lean#L670); the definition falls back to zero
  if no unique polynomial exists. There is no separately selected
  Van Vleck polynomial function.

## Chapter 32 — Painlevé transcendents

Traversal: all §§32.1–32.17 checked; matching headings are §§32.4(i)
and 32.7(i). The six equations in §32.2 are complementary entries.
Names below are in `DLMF.Painleve`.

### Complementary §32.2: Differential equations

- **Painlevé I–VI and transformed Painlevé III′**,
  [32.2.1–6 and 32.2.8](https://dlmf.nist.gov/32.2.E1):
  `painleveIRhs`, `painleveIIRhs`, `painleveIIIRhs`, `painleveIVRhs`,
  `painleveVRhs`, `painleveVIRhs`, `painleveIIIPrimeRhs`, with predicates
  `IsPainleveIOn`, `IsPainleveIIOn`, `IsPainleveIIIOn`, `IsPainleveIVOn`,
  `IsPainleveVOn`, `IsPainleveVIOn`, `IsPainleveIIIPrimeOn`, in
  [Defs](DLMF/Painleve/Defs.lean#L106). The predicates retain the required
  nonvanishing denominators, rather than merely totalizing rational right
  sides. These specify families of solutions, not selected generic
  transcendents. The older `IsPIIOn c` in
  [Basic](DLMF/Painleve/Basic.lean#L54) uses the Beals–Wong parameter c=−α.

### §32.4(i): Isomonodromy-problem definition

- **Lax pair and compatibility / zero curvature**,
  [32.4.1–3](https://dlmf.nist.gov/32.4.E1): there is no general local
  predicate selecting a fundamental matrix or defining isomonodromy.
  Explicit coefficient matrices `painleveILaxA`, `painleveILaxB`,
  `painleveIILaxA`, `painleveIILaxB`, `painleveIIILaxM`,
  `painleveIIILaxA`, `painleveIIILaxB`, with `laxSigma1`, `laxSigma2`,
  `laxSigma3`, are in [Defs](DLMF/Painleve/Defs.lean#L279).
  The independent `laxA`, `laxB` in
  [LaxPair](DLMF/Painleve/LaxPair.lean#L42) use Beals–Wong's Painlevé-II
  spectral-variable and c=−α normalization. Matrix compatibility identities
  are theorems, not a construction of a global fundamental matrix or
  monodromy data.

### §32.7(i): Bäcklund-transformation definition

- **Bäcklund transformations**, [§32.7(i)](https://dlmf.nist.gov/32.7.i):
  DLMF's prose describes transformations between Painlevé solutions and
  parameter values; there is no abstract local `BacklundTransformation`
  structure. The explicit Painlevé-II transformations `painleveIITPlus`,
  `painleveIITMinus` for [32.7.2](https://dlmf.nist.gov/32.7.E2) are in
  [Defs](DLMF/Painleve/Defs.lean#L268). The independently organized
  Beals–Wong operations `backlundReflect`, `backlundDown`, `backlundUp`
  in [Backlund](DLMF/Painleve/Backlund.lean#L36) act on the c=−α family;
  these require that parameter conversion when compared with DLMF.

## Chapter 33 — Coulomb functions

Traversal: all §§33.1–33.26 checked; matching headings are §§33.2,
33.14 and 33.22(ii). The last is an application-specific variable dictionary,
recorded here because its heading matches, without acquiring physical models.

### §33.2: Definitions and basic properties

- **Coulomb equation and outer turning point ρₜₚ**,
  [33.2.1–2](https://dlmf.nist.gov/33.2.E1):
  `DLMF.Coulomb.turningPoint` in [Basic](DLMF/Coulomb/Basic.lean#L104).
  The differential equation is expressed in solution theorems rather than a
  separate named Coulomb-ODE predicate.
- **Regular Coulomb Fℓ and normalizing Cℓ**,
  [33.2.3–6](https://dlmf.nist.gov/33.2.E3):
  `DLMF.Confluent.coulombF`, `coulombC`, and the unnormalized complex
  `coulombWave`, with `coulombWaveDeriv`, in
  [Basic](DLMF/Coulomb/Basic.lean#L44). The real function is the real part
  of C times the native Kummer-M formula. The Whittaker form is a bridge,
  not a second defined F. A genuinely wider complex-parameter definition
  `DLMF.Coulomb.coulombWaveComplex` is in
  [Defs](DLMF/Coulomb/Defs.lean#L147); this remains unnormalized and uses a
  principal power for complex ℓ. It agrees with `coulombWave` at natural ℓ;
  comparison with F also needs the real normalization Cℓ.
- **Outgoing/incoming Hℓ± and irregular Gℓ**,
  [33.2.7–8 and 33.2.11](https://dlmf.nist.gov/33.2.E7):
  `DLMF.Confluent.coulombHPlus`, `coulombHMinus`, `coulombG` in
  [Basic](DLMF/Coulomb/Basic.lean#L78), actual Kummer-U formulas followed
  by real part for G. `coulombAPlus` exposes the coefficient of the
  unscaled U form. Whittaker-W representations are bridges.
- **Coulomb phase θℓ and phase shift σℓ**,
  [33.2.9–10](https://dlmf.nist.gov/33.2.E9):
  `DLMF.Confluent.coulombTheta`, `coulombSigma` in
  [Basic](DLMF/Coulomb/Basic.lean#L69) use the principal `Complex.arg` of
  Gamma. The separate `DLMF.Coulomb.phaseShift` in
  [Defs](DLMF/Coulomb/Defs.lean#L62) is an arctangent series and finite
  sum, implementing DLMF's continuous phase with value zero at η=0.
  These are not equal as real-valued phase functions globally; their
  exponentials are compared by `exp_I_phaseShift` in
  [RhoEtaProperties](DLMF/Coulomb/RhoEtaProperties.lean#L513).

### §33.14: Definitions and basic properties

Names in this subsection are in `DLMF.Coulomb`.

- **Energy/radius variables ε,r and κ, and turning point rₜₚ**,
  [33.14.1–3 and 33.14.6](https://dlmf.nist.gov/33.14.E2):
  `coulombKappa`, `turningPointR` in
  [Energy/Defs](DLMF/Coulomb/Energy/Defs.lean#L65).
  The change r=−ηρ, ε=1/η² is used as an expression, without separate
  conversion objects. κ uses the upper imaginary sign when ε>0 and the
  sign of r when ε<0; ε=0 has a fallback value.
- **Regular f(ε,ℓ;r)**, [33.14.4–5](https://dlmf.nist.gov/33.14.E4):
  `coulombfKummer`, `coulombf` in
  [Energy/Defs](DLMF/Coulomb/Energy/Defs.lean#L72). For nonzero ε the
  definition takes the real part of the Kummer formula; ε=0 is filled by
  a regularized ₀F₁ expression. The Whittaker and Bessel forms are
  representations of this function, not additional selected functions.
- **Irregular h and piecewise S(ε,r)**,
  [33.14.7–8](https://dlmf.nist.gov/33.14.E7): `coulombSFactor`,
  `coulombhKappa`, `coulombhFormula`, `coulombh` in
  [Energy/Defs](DLMF/Coulomb/Energy/Defs.lean#L90).
  The first two formula objects expose the Whittaker/Kummer construction;
  the final real function fills ε=0 and Gamma-pole parameters by
  `limUnder` in ε. Existence and the intended values of such limits need
  separate results; merely having the totalized limit object is not proof
  of analytic continuation. r=0 remains outside the intended domain.
- **Energy-normalized s,c and factors A,B**,
  [33.14.9–12](https://dlmf.nist.gov/33.14.E9): `coulombAProd`,
  `coulombBFactor`, `coulombs`, `coulombc` in
  [Energy/Defs](DLMF/Coulomb/Energy/Defs.lean#L125).
  A is the finite product; its Gamma ratio is a theorem bridge. The
  functions s,c are complex and retain the principal powers when B<0,
  as required by DLMF; c at B=0 is totalized.
- **Hydrogenic radial φₙ,ℓ**, [33.14.14](https://dlmf.nist.gov/33.14.E14):
  `hydrogenRadial` in [Energy/Defs](DLMF/Coulomb/Energy/Defs.lean#L157),
  defined from f at ε=−1/n² and real normalization factors. The Laguerre
  expression is an equivalence theorem, for the DLMF range n≥ℓ+1.

### §33.22(ii): Definitions of variables

- **k-scaled ρ,η; Z-scaled r,ε; ik-scaled z,κ; Bohr and Rydberg scales**,
  [33.22.4–6 and intervening prose](https://dlmf.nist.gov/33.22.E4):
  no project definitions of these physical scalings, particle masses,
  charges or constants were found. Their mathematical Coulomb arguments
  are supplied directly to the objects above. This is application
  notation, not an omitted numerical approximation implementation.

## Chapter 34 — 3j, 6j, 9j symbols

Traversal: all §§34.1–34.15 checked; matching headings are §§34.2,
34.4 and 34.6. Names below are in `DLMF.WignerSymbols`.

### §34.2: Definition: 3j symbol

- **Angular momenta, triangle conditions and projection quantum numbers**,
  [34.2.1–3 and prose](https://dlmf.nist.gov/34.2.E1): `IsAngularMomentum`,
  `IsTriad`, `IsProjection`, `IsAdmissible3j`, with finite range
  `projections`, in [Basic](DLMF/WignerSymbols/Basic.lean#L62).
  j and m are rational, with integrality and parity expressed by predicates;
  `IsTriad` includes the integer-sum restriction, beyond real triangle
  inequalities alone.
- **Wigner 3j and triangle coefficient Δ**,
  [34.2.4–5](https://dlmf.nist.gov/34.2.E4): `wigner3j`, `triangleDelta`,
  with `racahTerm3j`, `factQ`, `invFactQ`, `signPow`, in
  [Basic](DLMF/WignerSymbols/Basic.lean#L113). This is the finite Racah
  sum; negative factorial arguments make reciprocal-factorial summands
  zero. Inadmissible projections are extended by zero. The ₃F₂ expression
  34.2.6 is a bridge theorem rather than a second 3j definition.

### §34.4: Definition: 6j symbol

- **Wigner 6j**,
  [34.4.1–3](https://dlmf.nist.gov/34.4.E1): `wigner6j`,
  `IsAdmissible6j`, `racahTerm6j` in
  [Basic](DLMF/WignerSymbols/Basic.lean#L169), defined by the single
  Racah sum 34.4.2 and zero outside the four triads. The product-of-four-3j
  definition 34.4.1 is theorem `wigner6j_eq_sum_threeJ` in
  [SixJ](DLMF/WignerSymbols/SixJ.lean), not another defined object;
  the terminating ₄F₃ expression is likewise a bridge.

### §34.6: Definition: 9j symbol

- **Wigner 9j**, [34.6.1–2](https://dlmf.nist.gov/34.6.E1): `wigner9j`
  in [Basic](DLMF/WignerSymbols/Basic.lean#L199), the finite sum of three
  6j symbols over half-integer j. The six-3j expression is theorem
  `wigner9j_eq_sum_threeJ` in [NineJ](DLMF/WignerSymbols/NineJ.lean).
  No independent three-variable hypergeometric 9j object is defined.

## Chapter 35 — Functions of matrix argument

Traversal: all §§35.1–35.12 checked; matching headings are the Definition
paragraph of §35.2 and §§35.3(i), 35.4(i), 35.5(i), 35.6(i), 35.7(i),
35.8(i). Names below are in `DLMF.MatrixArgument` unless qualified.

The definitions use real symmetric matrices, the positive-definite cone,
and Lebesgue measure on the independent upper-triangular entries. The
supporting §35.1 notation has actual objects `SymMatrix`, `posDefCone`,
`matrixInterval`, `etr`, `leadingMinor`, `matrixSpectralNorm`,
`orthogonalHaar` in [Basic](DLMF/MatrixArgument/Basic.lean#L78).
The measure is upstream `TauCeti.symmetricLebesgue`; its precise dependency
and normalization are recorded in
[MathlibCoverage](DLMF/MatrixArgument/MathlibCoverage.lean#L12).

### §35.2: Laplace-transform definition

- **Matrix Laplace transform**, [35.2.1](https://dlmf.nist.gov/35.2.E1):
  `laplaceTransform` in [Basic](DLMF/MatrixArgument/Basic.lean#L309), the
  cone integral with a complex symmetric matrix argument Z.
  `complexSymmetricOfCoords` in
  [Basic](DLMF/MatrixArgument/Basic.lean#L112) parametrizes its independent
  complex entries. The inversion formula 35.2.2 is a theorem, not another
  defined transform.
- **Matrix convolution**, [35.2.3](https://dlmf.nist.gov/35.2.E3):
  `matrixConvolution` in [Basic](DLMF/MatrixArgument/Basic.lean#L317),
  integrating over 0<X<T. This is a definition later in the same section,
  outside the first paragraph titled Definition.

### §35.3(i): Definitions

- **Multivariate Γₘ(a), generalized Γₘ(s₁,…,sₘ), and Bₘ(a,b)**,
  [35.3.1–3](https://dlmf.nist.gov/35.3.E1): `multivariateGamma`,
  `multivariateGammaVec`, `multivariateBeta` in
  [Basic](DLMF/MatrixArgument/Basic.lean#L168). These are Gamma products
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

### §35.4(i): Definitions

- **Partition κ, weight |κ|, length ℓ(κ), and a+κ**,
  [opening prose](https://dlmf.nist.gov/35.4.i): `partitions`,
  `partitionLength`, `nextPart` in
  [Basic](DLMF/MatrixArgument/Basic.lean#L142). A partition here is a
  nonincreasing vector `Fin m → ℕ`; its weight and shift are finite-sum
  and pointwise expressions. This representation differs from the
  integer-partition objects in Chapter 26.
- **Partitional shifted factorial [a]κ**,
  [35.4.1](https://dlmf.nist.gov/35.4.E1): `partitionalShiftedFactorial`
  in [Basic](DLMF/MatrixArgument/Basic.lean#L158), the product of scalar
  ascending Pochhammer polynomials, with zero-based shift j/2.
- **Zonal polynomial Zκ and normalization Zκ(I)**,
  [35.4.2–3](https://dlmf.nist.gov/35.4.E2): `zonalPolynomialAtOne`,
  `zonalPolynomial` in [Basic](DLMF/MatrixArgument/Basic.lean#L193).
  The actual definition uses normalized Haar integration over O(m) and
  powers of leading minors, combining the final determinant factor into
  the product. The intended domain is symmetric T and nonincreasing κ;
  the Lean formula is also evaluable elsewhere. DLMF's Cκ, 𝒴κ and Φκ
  in the closing prose are alternative notation, not extra local objects.

### §35.5(i): Definitions

- **Matrix Bessel Aν and Bν**, [35.5.1–3](https://dlmf.nist.gov/35.5.E1):
  `besselA`, `besselB` in [Basic](DLMF/MatrixArgument/Basic.lean#L261).
  A uses its normalized zonal-polynomial series; B is a cone integral with
  the inverse-matrix exponential. The normalization at zero is the reciprocal
  multivariate Gamma expression, not a separately defined constant.
  At exceptional denominator parameters the A-series definition is
  totalized; any continued regularization needs a separate theorem.

### §35.6(i): Definitions

- **Matrix ₁F₁ and Ψ**, [35.6.1–2](https://dlmf.nist.gov/35.6.E1):
  `hyp1F1`, `kummerPsi` in [Basic](DLMF/MatrixArgument/Basic.lean#L241).
  The first wraps the partition series `hypergeometricPFQ`; Ψ is an
  independent cone-integral construction with Re a>(m−1)/2 and T positive
  definite. There is no separate global analytic continuation of that
  integral in this definition layer.
- **Matrix Laguerre form Lν⁽γ⁾**, [35.6.3](https://dlmf.nist.gov/35.6.E3):
  `laguerreL` in [Basic](DLMF/MatrixArgument/Basic.lean#L292), the Gamma
  ratio times ₁F₁, with complex degree ν rather than just a polynomial index.

### §35.7(i): Definition

- **Matrix ₂F₁**, [35.7.1](https://dlmf.nist.gov/35.7.E1): `hyp2F1` in
  [Basic](DLMF/MatrixArgument/Basic.lean#L248), a wrapper for the native
  partition series, interpreted on ‖T‖<1 and nonexceptional c.
- **Matrix Jacobi form Pν⁽γ,δ⁾**, [35.7.2](https://dlmf.nist.gov/35.7.E2):
  `jacobiP` in [Basic](DLMF/MatrixArgument/Basic.lean#L300), the stated
  Gamma-ratio/₂F₁ construction; DLMF requires 0<T<I and Re γ>−1.

### §35.8(i): Definition

- **Generalized hypergeometric function of matrix argument**,
  [35.8.1](https://dlmf.nist.gov/35.8.E1): `hypergeometricPFQ` in
  [Basic](DLMF/MatrixArgument/Basic.lean#L223), an infinite sum over weights
  of finite sums over partitions. `hyp0F0`, `hyp1F0`, `hyp0F1`, `hyp1F1`,
  `hyp2F1`, `hyp3F2` in the same file are parameter-list wrappers.
  Denominator partitional factorials must not vanish. The convergence
  distinctions p≤q, p=q+1 and p>q+1 are separate properties; a divergent
  totalized sum is not an analytic continuation.

## Chapter 36 — Integrals with coalescing saddles

Traversal: all §§36.1–36.15 checked; matching headings are §§36.2(i)
and 36.5(i). Names below are in `DLMF.CoalescingSaddles`.

### §36.2(i): Definitions

- **Cuspoid, elliptic-umbilic and hyperbolic-umbilic normal forms**,
  [36.2.1–3](https://dlmf.nist.gov/36.2.E1): `cuspoidPotential`,
  `ellipticUmbilicPotential`, `hyperbolicUmbilicPotential` in
  [Basic](DLMF/CoalescingSaddles/Basic.lean#L73). Variables are complex,
  control parameters real. K=1,2,3 in `cuspoidPotential` express fold,
  cusp and swallowtail; these are not extra selected functions.
- **Canonical integrals ΨK, Ψ⁽ᴴ⁾, Ψ⁽ᴱ⁾**,
  [36.2.4–5](https://dlmf.nist.gov/36.2.E4): `cuspoidIntegral`,
  `hyperbolicUmbilicIntegral`, `ellipticUmbilicIntegral` in
  [Basic](DLMF/CoalescingSaddles/Basic.lean#L129).
  They use absolutely convergent rotated contours or cycles rather than
  the totalized Lebesgue integral of the conditionally convergent real
  oscillation. The contour data are `cuspoidAngle`, `cuspoidContourDir`,
  `cuspoidContour`, `ellipticUmbilicRayDir`, `ellipticUmbilicCycle`,
  `ellipticUmbilicPotentialAB`, `ellipticUmbilicQuadrant` in the same file.
  Alternative one-dimensional contour and Airy representations
  [36.2.6–9](https://dlmf.nist.gov/36.2.E6) are bridge theorems in
  [OscillatoryRepresentations](DLMF/CoalescingSaddles/CanonicalIntegrals/OscillatoryRepresentations.lean#L580).
  The F± integrals of 36.2.7 are local expressions in the corresponding
  theorem, not additional globally defined objects.
- **Diffraction catastrophes ΨK(x;k), Ψ⁽ᵁ⁾(x;k)**,
  [36.2.10–11](https://dlmf.nist.gov/36.2.E10): `cuspoidDiffraction`,
  `hyperbolicUmbilicDiffraction`, `ellipticUmbilicDiffraction` in
  [Basic](DLMF/CoalescingSaddles/Basic.lean#L161). These use the same
  decaying contours with k in the exponential and the DLMF √k or k factor;
  their intended domain is k>0.

### §36.5(i): Definitions

- **Steepest-descent saddle connection and Stokes sets**,
  [36.5.1 and prose](https://dlmf.nist.gov/36.5.E1):
  `IsSaddleConnection`, `IsSaddleConnection₂`, `cuspoidStokesSet`,
  `umbilicStokesSet`, `cuspoidComplexStokesSet`, `umbilicComplexStokesSet`
  in [Basic](DLMF/CoalescingSaddles/Basic.lean#L256).
  These require distinct critical points connected by a continuous path
  of constant real phase, not just equality of endpoint real parts.
  The first two sets require a real and a nonreal saddle; the separate
  complex-saddle variants exclude conjugate pairs and implement DLMF's
  explicitly identified extensions beyond the main real-saddle convention.



## Traversal counts and interpretation

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

Only Chapters 3, 12 and 17 have no matching title. Complementary entries in
Chapters 4, 7, 9, 12, 16, 17 and 32 are labelled and do not change those counts.
The Chapter 31 fundamental-equation entries are also complementary. This
catalogue does not claim to enumerate every definition under every other DLMF
heading, nor to enumerate every implementation helper in the Lean sources.

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
