# lean-DLMF: Special Functions following the DLMF

A Lean 4 formalization of special functions following the NIST Digital Library of
Mathematical Functions (DLMF). The project began as a formalization of Andrews, Askey and
Roy, *Special Functions* (1999), henceforth AAR, and was renamed from lean-AAR to lean-DLMF
on 2026-10-21, when the DLMF chapters became its organizing principle. AAR, Temme,
Beals–Wong and Duverney remain supporting sources.

## Organization

The older areas follow the chapter arrangement of AAR; the newer ones are organized by DLMF
chapter, with the supporting source shown in parentheses below. Its aim is to fill gaps in
Mathlib's coverage of special functions, not to reproduce either source sequentially. Each
umbrella module `DLMF/<Area>.lean` describes what Mathlib already provides and what the
area adds. Statements taken from the DLMF record their equation numbers with Mathlib's
`@[dlmf]` cross-reference attribute.

`DLMF.lean` imports all areas. The current library has 1,199 Lean files, including
109 general supporting modules and the two library root entry points. Large topic modules
are split into mathematical subtopics; the former file remains as a small import umbrella.
For example, `Gamma/IntegralRepresentations.lean` now imports the Hankel, Prym, Binet and
moment modules below `Gamma/IntegralRepresentations/`.
Every Lean source file is at most 1,500 lines; run `python3 scripts/check_file_lengths.py`
to enforce this limit. The complete split map and the structural cleanup snapshot are in
[CodeReviewInventory.json](CodeReviewInventory.json), with the mathematical review in
[REVIEW.md](REVIEW.md). The chapter-by-chapter correspondence between DLMF definitions
and actual Lean constructions is recorded in [DEFINITIONS.md](DEFINITIONS.md).
[DEFINITIONS2.md](DEFINITIONS2.md) expands that inventory to definitions introduced
throughout the DLMF, in source order, including auxiliary objects and definitions in prose.
Both catalogues record missing counterparts and differences in domains and branches.

For a view of the organized foundations, use `import DLMF.Basic`. It imports all
59 area and subarea `Basic.lean` entry points. Each is a small foundational file or
an umbrella over descriptive files under `Basic/`, such as
`Confluent/Basic/IncompleteGamma.lean` and `Mathieu/Basic/Spectral.lean`.
This layer contains canonical definitions and their necessary elementary support;
it has no dependencies on DLMF theorem files. The complete area umbrellas continue
to expose their theorem developments. The foundation entry point is a coherent
import layer, while the definition catalogues remain the fuller mathematical inventory.

The [foundation reorganization](REVIEW.md#foundational-basic-layer-2026-10-30)
moves legacy `Defs.lean`, `SolutionsDefs.lean` and `FerrersDefs.lean` modules into
this layout and gives former theorem-heavy `Basic` files descriptive theorem names.
Lean declaration names and namespaces are preserved; some module import paths change.
The module migration map and preservation checks are recorded in
[OrganizationRound20261030.json](OrganizationRound20261030.json).

Source files below each area directory, including nested topic modules and compatibility
umbrellas (2026-10-30):

- [Airy](DLMF/Airy.lean): 41 files.
- [AlgebraicAnalytic](DLMF/AlgebraicAnalytic.lean): 53 files.
- [AsymptoticApproximations](DLMF/AsymptoticApproximations.lean): 30 files.
- [BernoulliEuler](DLMF/BernoulliEuler.lean): 21 files.
- [Bessel](DLMF/Bessel.lean): 29 files.
- [CoalescingSaddles](DLMF/CoalescingSaddles.lean): 17 files.
- [Combinatorics](DLMF/Combinatorics.lean): 30 files.
- [Confluent](DLMF/Confluent.lean): 64 files.
- [Constants](DLMF/Constants.lean): 3 files.
- `Core`: 5 files.
- [Coulomb](DLMF/Coulomb.lean): 15 files.
- [Elementary](DLMF/Elementary.lean): 23 files.
- [Elliptic](DLMF/Elliptic.lean): 13 files.
- [EllipticIntegrals](DLMF/EllipticIntegrals.lean): 32 files.
- [ErrorFunctions](DLMF/ErrorFunctions.lean): 20 files.
- [ExpIntegrals](DLMF/ExpIntegrals.lean): 11 files.
- [Gamma](DLMF/Gamma.lean): 49 files.
- [GeneralizedHypergeometric](DLMF/GeneralizedHypergeometric.lean): 25 files.
- [Heun](DLMF/Heun.lean): 9 files.
- [Hypergeometric](DLMF/Hypergeometric.lean): 54 files.
- [IncompleteGamma](DLMF/IncompleteGamma.lean): 24 files.
- [JacobiElliptic](DLMF/JacobiElliptic.lean): 34 files.
- [Lame](DLMF/Lame.lean): 23 files.
- [Legendre](DLMF/Legendre.lean): 60 files.
- [Mathieu](DLMF/Mathieu.lean): 54 files.
- [MatrixArgument](DLMF/MatrixArgument.lean): 9 files.
- [NumberTheory](DLMF/NumberTheory.lean): 13 files.
- [OrthogonalPolynomials](DLMF/OrthogonalPolynomials.lean): 61 files.
- [Painleve](DLMF/Painleve.lean): 25 files.
- [ParabolicCylinder](DLMF/ParabolicCylinder.lean): 30 files.
- [Polylog](DLMF/Polylog.lean): 3 files.
- [QHypergeometric](DLMF/QHypergeometric.lean): 15 files.
- [QSeries](DLMF/QSeries.lean): 11 files.
- [RiemannTheta](DLMF/RiemannTheta.lean): 9 files.
- [Selberg](DLMF/Selberg.lean): 7 files.
- [SphericalHarmonics](DLMF/SphericalHarmonics.lean): 5 files.
- [Spheroidal](DLMF/Spheroidal.lean): 17 files.
- [Statistical](DLMF/Statistical.lean): 6 files.
- [Struve](DLMF/Struve.lean): 30 files.
- [Theta](DLMF/Theta.lean): 13 files.
- [WaveEquation](DLMF/WaveEquation.lean): 1 file.
- [Weierstrass](DLMF/Weierstrass.lean): 18 files.
- [WignerSymbols](DLMF/WignerSymbols.lean): 7 files.
- [Zeta](DLMF/Zeta.lean): 23 files.

The single-file areas [Bailey](DLMF/Bailey.lean) and [Partitions](DLMF/Partitions.lean)
retain their entry modules. Supporting-source areas include `Constants`, `Polylog`,
`Statistical`, `Elliptic`, `WaveEquation`, `Selberg` and `SphericalHarmonics`; their module
headers record the relevant AAR, Temme, Beals–Wong or Duverney sources. The DLMF chapter
entry points and acquisition ledgers are described below.

The new chapter entry points are [Elementary](DLMF/Elementary.lean) (Chapter 4),
[GeneralizedHypergeometric](DLMF/GeneralizedHypergeometric.lean) (Chapter 16,
including Appell and Meijer G), and [QHypergeometric](DLMF/QHypergeometric.lean)
(Chapter 17). Their acquisition ledgers are [Chapter 4](DLMF4Acquisition.md),
[Chapter 16](DLMF16Acquisition.md), and [Chapter 17](DLMF17Acquisition.md).
They include mathematical prose and exact tables; graphics, application notes and
purely numerical data are excluded. Each chapter has checked upstream coverage;
new proof obligations remain explicit.

Chapter 19 (elliptic integrals: Legendre's and Carlson's symmetric forms), acquired on
2026-10-25, has the entry point [EllipticIntegrals](DLMF/EllipticIntegrals.lean) and the ledger
[Chapter 19](DLMF19Acquisition.md). It builds on the existing real `DLMF.Elliptic` integrals,
the complex K of `DLMF.JacobiElliptic`, and the proved Carlson library of lean-codes.

The theta and elliptic-function chapters, acquired on 2026-10-25, have the entry points
[Theta](DLMF/Theta.lean) (Chapter 20), [RiemannTheta](DLMF/RiemannTheta.lean)
(Chapter 21), [JacobiElliptic](DLMF/JacobiElliptic.lean) (Chapter 22) and
[Weierstrass](DLMF/Weierstrass.lean) (Chapter 23, including modular functions).
Their ledgers are [Chapter 20](DLMF20Acquisition.md), [Chapter 21](DLMF21Acquisition.md),
[Chapter 22](DLMF22Acquisition.md) and [Chapter 23](DLMF23Acquisition.md). They build on
the existing `DLMF.Elliptic` theta and real Jacobi APIs and on Mathlib's `jacobiTheta₂`,
Weierstrass `PeriodPair`, Dedekind eta and discriminant. Applications, graphics,
computation, tables and software sections are excluded; the ledgers list the purely
mathematical results found in excluded Applications sections.

Chapters 24–27, acquired on 2026-10-25, have the entry points
[BernoulliEuler](DLMF/BernoulliEuler.lean) (Chapter 24, Bernoulli and Euler polynomials),
[Zeta](DLMF/Zeta.lean) (Chapter 25, zeta and related functions),
[Combinatorics](DLMF/Combinatorics.lean) (Chapter 26, combinatorial analysis) and
[NumberTheory](DLMF/NumberTheory.lean) (Chapter 27, functions of number theory), with the
ledgers [Chapter 24](DLMF24Acquisition.md), [Chapter 25](DLMF25Acquisition.md),
[Chapter 26](DLMF26Acquisition.md) and [Chapter 27](DLMF27Acquisition.md). They reuse
Mathlib's Bernoulli numbers and polynomials, Riemann and Hurwitz zeta, `expZeta`, Dirichlet
L-functions, binomial, Catalan, Bell and Stirling numbers, partitions, permutations,
arithmetic functions, characters and reciprocity, recorded with `dlmf_upstream` pointers.
The same exclusions apply; open conjectures (Riemann hypothesis, Goldbach, Lehmer) are named
as propositions, never stated as theorems.

Chapters 28–31, acquired on 2026-10-26, have the entry points
[Mathieu](DLMF/Mathieu.lean) (Chapter 28, Mathieu functions and Hill's equation),
[Lame](DLMF/Lame.lean) (Chapter 29, Lamé functions),
[Spheroidal](DLMF/Spheroidal.lean) (Chapter 30, spheroidal wave functions) and
[Heun](DLMF/Heun.lean) (Chapter 31, Heun functions), with the ledgers
[Chapter 28](DLMF28Acquisition.md), [Chapter 29](DLMF29Acquisition.md),
[Chapter 30](DLMF30Acquisition.md) and [Chapter 31](DLMF31Acquisition.md). Mathlib has none of
these functions. Explicit constructions are used where they exist (Heun's local solution, Lamé
and Ince polynomials, Bessel-product series); otherwise the solutions and eigenvalues are chosen
from flagged existence theorems, which are proof targets. The same exclusions apply.

Chapter 32 (Painlevé transcendents), acquired on 2026-10-26, extends the entry point
[Painleve](DLMF/Painleve.lean) with the six Painlevé equations in DLMF's normalization,
Hamiltonian structure, Bäcklund transformations, rational, elementary and special-function
solutions, real asymptotics and PDE reductions (ledger [Chapter 32](DLMF32Acquisition.md)).
DLMF's PII with parameter α is the Beals–Wong PII(−α) of the older modules described below.

Chapters 33–36, the final four chapters of the DLMF, were acquired on 2026-10-26 as four new
entry points: [Coulomb](DLMF/Coulomb.lean) (Chapter 33; the existing Coulomb functions of the
Confluent area moved down unchanged into `DLMF/Coulomb/Basic.lean`; the r, ε functions in
`DLMF/Coulomb/Energy`), [WignerSymbols](DLMF/WignerSymbols.lean) (Chapter 34; 3j, 6j and 9j
symbols with rational quantum numbers), [MatrixArgument](DLMF/MatrixArgument.lean) (Chapter 35;
Tau Ceti's measure on symmetric matrices, zonal polynomials from DLMF 35.4.2–35.4.3,
hypergeometric functions of matrix argument as sums over partitions) and
[CoalescingSaddles](DLMF/CoalescingSaddles.lean) (Chapter 36; canonical integrals as absolutely
convergent integrals along rotated contours). Ledgers: [Chapter 33](DLMF33Acquisition.md),
[Chapter 34](DLMF34Acquisition.md), [Chapter 35](DLMF35Acquisition.md),
[Chapter 36](DLMF36Acquisition.md). Applications, computation, graphics and numerical values are
excluded, as elsewhere.

Chapters 1 and 2, the general methods chapters, were acquired on 2026-10-27 as two new entry
points, completing the set of chapter entry points (Chapter 3, numerical methods, is out of scope):
[AlgebraicAnalytic](DLMF/AlgebraicAnalytic.lean) (Chapter 1; algebra, calculus, Fourier series,
complex variables, zeros of polynomials, continued fractions, differential equations, integral
transforms, summability, distributions and spectral theory) and
[AsymptoticApproximations](DLMF/AsymptoticApproximations.lean) (Chapter 2; order symbols,
Watson's lemma, Laplace, stationary-phase and Mellin methods, distributional methods,
Liouville–Green approximation, Euler–Maclaurin and Darboux, Stokes phenomenon). Much of
Chapter 1 is standard mathematics already in Mathlib or Tau Ceti and is recorded through
`dlmf_upstream` pointers rather than reproved. Ledgers: [Chapter 1](DLMF1Acquisition.md),
[Chapter 2](DLMF2Acquisition.md).

DLMF errata and source corrections found anywhere in the project are collected in
the [DLMF errata report](https://bjbraams.github.io/lean-DLMF/DLMFErrata.pdf) (LaTeX source
[reports/DLMFErrata.tex](reports/DLMFErrata.tex), built by CI and published on GitHub Pages):
genuine DLMF errata, fixed transcription defects of our own, and formalization notes, each with
evidence and the Lean declarations.

Since 2026-10-25 the companion project [lean-codes](../lean-codes) is a Lake dependency
(package `LeanCodes`); its Carlson library underlies Chapter 19. The project's own general
library was renamed from `ToMathlib` to `DLMFMathlib` at the same time, since the `ToMathlib`
prefix belongs to lean-codes (see AGENTS.md).

The [Beals–Wong inventory](BealsWongInventory.md) records further special-function
gaps and their implementation status. The 18 October 2026 additions prove discrete
polynomial addition identities, Rodrigues formulas for the four classical discrete
families, strict indexed Hermite/Jacobi zero bounds, and Gaussian/Laplace Bessel
transforms with complex scale and regularized exceptional-order coverage. See
[the review](REVIEW.md) for parameter restrictions and validation.

[Painlevé II](DLMF/Painleve.lean), following Beals–Wong Chapter 15, adds local
real existence and uniqueness, Bäcklund transformations, rational solutions
at every integer parameter, and meromorphic Airy-based solutions at every
half-integer parameter. It also proves conditional pole/residue restrictions,
Lax compatibility, and the tau-quotient converse. Global continuation, Stokes
theory, and the real connection formulas remain open; see the
[inventory](BealsWongInventory.md#chapter-15-painlevé-transcendents).

## Naming conventions for special functions

- **Reciprocals use `recip` or `reciprocal` in project-defined names**, including
  `recipGammaDeriv`, `zRecipDeriv`, and reciprocal-factorial expansions. Reserve
  `inverse` for functional, compositional, or operator inverses. Imported Lean,
  Mathlib and TauCeti identifiers retain their upstream spelling.
- **Names follow DLMF via Miller's content-dictionary proposal** (Miller, *RFC: DLMF Content
  Dictionaries*, NIST 2018, in `References/`), adapted to Mathlib: lowerCamelCase with Mathlib's
  capitalization, Mathlib's names where Mathlib already has the function, project namespaces,
  correct spellings (Appell, Carlson), and redundant words dropped.
- **Plain name: the analytic continuation** on its standard domain, which is named by a domain
  predicate (`slitPlane`, `cutPlane`, `{z | 1 + z ∈ slitPlane}`, …) in the docstring and in theorem
  hypotheses. Examples: `regularizedGaussHG` (on `cutPlane`), `kummerU`, `erf`, `besselJ`.
- **`…Series` / `…Integral`: the native representation**, when it is a separate definition with its
  own natural domain. Examples: `regularizedGaussHGIntegral` (Euler's integral), `polylogSeries`
  (on the closed disc), `compEllIntKkSeries` (`₂F₁` in the modulus). The plain name is reserved
  for the continuation even when that is not defined yet, as for `polylog`.
- **Real-variable forms live in a `Real` sub-namespace** of the area namespace, mirroring Mathlib's
  `Real.Gamma`/`Complex.Gamma`: `DLMF.Polylog.Real.dilog`, `DLMF.Confluent.Real.sinInt`,
  `DLMF.Statistical.Real.incBeta`. Their lemmas are `Real.hasDerivAt_dilog`, `Real.dilog_one`, ….
- **Elliptic functions carry their argument convention as the last letter**, following Miller:
  `k` for the modulus, `m = k²` for the parameter, `Tau` or `Q` for theta functions in `τ` or in
  the nome `q`, and `Null` for theta constants (`z = 0`). Argument order is DLMF's.
- **Bridge theorems** are named `X_eq_XSeries`, `X_eq_XIntegral`, or after the real form, with the
  domain as hypothesis. Examples: `regularizedGaussHG_eq_regularizedGaussHGIntegral`,
  `polylogSeries_two_ofReal_eq_dilog`. Bridges to an upstream series use the upstream name, as in
  `regularizedGaussHG_eq_regularizedGaussHGFun` (Mathlib's `regularizedGaussHGFun` is the series).

- Kummer `M(a,b,z)`, `U(a,b,z)` (13.2): `kummerM`, `kummerU` (Miller: `KummerconfhyperM`, `KummerconfhyperU`).
- Whittaker `M_{κ,μ}`, `W_{κ,μ}` (13.14): `whittakerM`, `whittakerW` (Miller: `WhittakerconfhyperM`, `…W`).
- Hankel `H^{(1)}_ν`, `H^{(2)}_ν` (10.4): `hankelH1`, `hankelH2` (Miller: `HankelH1`, `HankelH2`).
- Modified Bessel `I_ν`, `K_ν` (10.25): `besselI`, `besselK` (Miller: `modBesselI`, `modBesselK`).
- Legendre `P_ν`, `Q_ν` (14.3): `legendreP`, `legendreQ` (Miller: `assLegendreP`, `assLegendreQ`).
- Ferrers `𝖯_ν^μ` (14.3): `ferrersP` (Miller: `FerrersP`).
- Classical OPs (18.3): `jacobiPolyP`, `ultrasphPoly`, `legendrePolyP`, `laguerrePolyL`, `hermitePolyH` (Miller: `JacobipolyP`, …, `HermitepolyH`).
- `γ(a,z)`, `Γ(a,z)` (8.2): `lowerIncGamma`, `upperIncGamma` (Miller: `incgamma`, `incGamma`).
- `P(a,z)`, `Q(a,z)`, `γ*(a,z)` (8.2): `normIncGammaP`, `normIncGammaQ`, `scIncGamma` (Miller: `normincGammaP`, `…Q`, `scincgamma`).
- `B_x(a,b)`, `I_x(a,b)` (8.17): `Real.incBeta`, `Real.normIncBetaI` (Miller: `incBeta`, `normincBetaI`).
- `erf`, `erfc`, Dawson `F` (7.2): `erf`, `erfc`, `Real.dawsonF` (Miller: `erf`, `erfc`, `DawsonintF`).
- Fresnel `C`, `S` (7.2): `Real.fresnelCosInt`, `Real.fresnelSinInt` (Miller: `Fresnelcosint`, `Fresnelsinint`).
- `Si`, `Ci`, `Cin`, `Ein`, `E_p` (6.2, 8.19): `Real.sinInt`, `Real.cosInt`, `Real.cosIntCin`, `Real.expIntEin`, `genExpIntE` (Miller: `sinint`, `cosint`, `cosintCin`, `expintEin`, `genexpintE`).
- `Li_s`, `Li₂`, `Li₃` (25.12): `polylogSeries`, `Real.dilog`, `Real.trilog` (Miller: `polylog`, `dilog`).
- Barnes `G`, `ψ^{(n)}`, `Γ_q`, `B_q`, `[n k]_q`: `barnesG`, `polygamma`, `qGamma`, `qBeta`, `qBinom` (Miller: `BarnesG`, `polygamma`, `qGamma`, `qBeta`, `qbinom`).
- `K`, `E`, `Π`, `D` complete (19.2.8): `compEllIntKk`/`…Km`, `compEllIntEk`/`…Em`, `compEllIntPik`/`…Pim`, `compEllIntDk`/`…Dm`; now `compEllIntKkSeries`, `Real.compEllIntKm`, `Real.compEllIntEm`, `Real.compEllIntPim` (Miller: `compellintKk`, `compellintEk`, `compellintPik`, `compellintDk`).
- `F(φ,k)`, `E(φ,k)`, `Π(φ,α²,k)` (19.2.4–7): `incEllIntFk`/`…Fm`, `incEllIntEk`/`…Em`, `incEllIntPik`/`…Pim`; now `Real.incEllIntFm`, `Real.incEllIntEm`, `Real.incEllIntPim` (Miller: `incellintFk`, `incellintEk`, `incellintPik`).
- `K′`, `E′` (19.2.9): `ccompEllIntKk`, `ccompEllIntEk` (planned) (Miller: `ccompellintKk`, `ccompellintEk`).
- `am`, `sn`, `cn`, `dn`, `arcsn` (22.2, 22.15, 22.16): complex `DLMF.JacobiElliptic.jacobiSnk`, … (all twelve) and `jacobiSnTau`, …; real `Real.jacobiAmm`, `Real.jacobiSnm`, `Real.jacobiCnm`, `Real.jacobiDnm`, `Real.jacobiArcsnm` (Miller: `Jacobiamk`, `Jacobiellsnk`, …, `aJacobiellsnk`).
- `θ_j(z\|τ)`, `θ_j(z,q)`, `θ_j(q)` (20.2): `jacobiThetaOneTau`, …, `jacobiThetaFourTau`; `DLMF.Theta.jacobiThetaOneQ`, …; `Real.jacobiThetaThreeNullQ`, `Real.jacobiThetaFourNullQ` (Miller: `Jacobithetatau`, `Jacobithetaq`).
- Carlson `R_F`, `R_D`, `R_C`, `R_J`, `R_G` (19.16): `carlsonRF`, … (planned) (Miller: `CarsonsymellintRF`, … (sic)).

The real digamma function is still `Real.digamma`, defined in Mathlib's `Real` namespace beside
Mathlib's `Complex.digamma`; moving it into `DLMF.Gamma.Real` is left for a later pass.

## Status

The [L'Hôpital, inverse-series and Appell reduction round](REVIEW.md#lhopital-hyperbolic-series-carlson-principal-values-and-appell-reductions-2026-10-30)
removes **9 admissions**, leaving **1,553**. It proves the unbounded-denominator L'Hôpital
rule, two hyperbolic inverse series, the negative-real RC principal-value formula and its
two-sided divergence limit, and four Appell reductions. Public theorem types and existing
mathematical definitions are unchanged. [ProofRound20261030f.json](ProofRound20261030f.json)
records validation and reusable support.

The [equality, inverse-series, Horn and elliptic round](REVIEW.md#holder-minkowski-equality-inverse-series-horn-pdes-and-elliptic-bounds-2026-10-30)
removes **14 admissions**, leaving **1,562**. It closes all remaining admissions in the
Chapter 1 inequalities file, proves the closed-disk arcsine/arccosine and Euler inverse
series, all four Horn G2/G3 PDEs, and four elliptic limit/bound declarations. One missing
pair of parentheses in the mixed Stieltjes formula is corrected and its intended formula
proved; a formal counterexample to the former transcription is preserved in the
[round report](ProofRound20261030e.json). All other existing theorem types and mathematical
definitions are retained.

The [inequality and Appell PDE round](REVIEW.md#inequalities-hyperbolic-integrals-appell-pdes-and-jacobi-epsilon-2026-10-30)
removes **15 admissions**, leaving **1,576**. It proves the finite Hölder converse, power-mean
bounds and order with equality cases, Schwarz's equality case, the coefficient circle-integral
formula, two hyperbolic integrals, all eight Appell PDE equations, the Jacobi amplitude
Maclaurin expansion and three epsilon integral identities. Existing statements and domains
are retained. [ProofRound20261030d.json](ProofRound20261030d.json) records validation,
reusable helpers and the next Horn PDE proof plan.

The [power-series and branch round](REVIEW.md#power-series-operations-branches-and-appell-nonseparability-2026-10-30)
removes **ten admissions**, leaving **1,591**. It completes reciprocal, logarithm and general
power coefficient convergence, the principal logarithmic sine and tangent series, the
cosh-square integral, two elliptic amplitude derivatives, all four Appell nonseparability
witnesses and a larger Horn G3 convergence region. General derivative and bivariate-series
lemmas support these proofs.
[ProofRound20261030c.json](ProofRound20261030c.json) records validation and a formal
counterexample to the existing mean-centered R-function series domain.

The [series, Carlson and Appell continuation](REVIEW.md#series-carlson-bounds-and-appell-transformations-2026-10-30)
removes **20 further admissions**, leaving **1,601**. It proves power-series differentiation
and Cauchy products, normalized logarithmic and boundary arctangent series, the tanh Frullani
integral, seven Carlson results, three Appell transformations, an asymptotic coefficient
recurrence and the Hurwitz zeta Taylor expansion. Existing statements and definitions are
unchanged. [ProofRound20261030b.json](ProofRound20261030b.json) records the checks and
reusable helpers.

The [analytic, elementary, elliptic and q-calculus round](REVIEW.md#analytic-elementary-elliptic-and-q-calculus-proofs-2026-10-30)
removes **24 admissions**, leaving **1,621**. It completes reversed Minkowski inequalities,
harmonic maximum principles, winding-number and Möbius results, elementary products and
logarithmic series, elliptic identities and limits, and q-derivative and modular-product
formulas. Existing statements and definitions are preserved. The
[round report](ProofRound20261030.json) records the source/type comparison, axiom audit,
validation and new statement issues, including three Lean-confirmed theta radius counterexamples.

The [Dougall, Lommel and Weierstrass round](REVIEW.md#dougall-lommel-and-weierstrass-proofs-2026-10-29)
removes **four admissions**, leaving **1,645**. It proves both terminating Dougall
summations, the capital Lommel differential equation at all parameters, and the
Weierstrass cosecant-series constant. All four statements and every existing definition
are unchanged. [ProofRound20261029f.json](ProofRound20261029f.json) records the compiled
axiom/type checks, reusable helpers and validation. The expanded definitions inventory
is [DEFINITIONS2.md](DEFINITIONS2.md).

The [later-chapter proof round](REVIEW.md#later-chapter-identities-and-series-2026-10-29)
removes **15 further admissions**, leaving **1,649**. It proves the full-domain q-Gauss sum,
classical coefficient limits, the Whittaker–Buchholz expansion, the Lommel parameter limit,
Carlson RC duplication, Weierstrass Fourier series and sigma products, the Bernoulli
Mellin–Barnes representation and the Narayana generating function. One sigma-product
statement was corrected at zeros of its prefactor; all other existing statements and
all existing definitions are unchanged. [ProofRound20261029e.json](ProofRound20261029e.json)
records the proofs, compatibility checks and validation.

The [Chapter 1–2 kernel, power-sum and Laplace-ray round](REVIEW.md#chapter-12-kernel-power-sum-and-laplace-ray-round-2026-10-29)
removes **three further admissions**, leaving **1,664**: **229** in Chapter 1 and **104** in
Chapter 2. It proves Watson's lemma for general rapidly decreasing kernels, the full
real-power sum expansion using the proved zeta Euler–Maclaurin formula, and the horizontal-ray
integral of the Laplace transform. The signed power-sum remainder bound remains admitted.
[ProofRound20261029d.json](ProofRound20261029d.json) records the proofs and validation.

The [Chapter 1–2 Fourier, Mellin and logarithmic Watson round](REVIEW.md#chapter-12-fourier-mellin-and-logarithmic-watson-round-2026-10-29)
removes **15 further admissions**, leaving **1,667**: **230** in Chapter 1 and **106** in
Chapter 2. It proves both Fourier-series Parseval pairings, smooth coefficient decay,
coefficient uniqueness, the complex Gaussian Poisson identity, the remaining Mellin pairings,
all four remaining Laplace-table entries, logarithmic Watson's lemma and three exact
Chapter 2 integrability or remainder results. One existing Mellin corollary also becomes
independent of admissions. [ProofRound20261029c.json](ProofRound20261029c.json) records the
proofs and validation; the review consolidates the five earlier statement issues.

The [Chapter 1–2 items 1–6 round](REVIEW.md#chapter-12-items-16-2026-10-29)
removes **28 admissions**: 16 in Chapter 1 and 12 in Chapter 2, leaving **1,682**.
It proves oscillatory and harmonic expansions, six exact transform entries, Fourier and
half-line Parseval identities, Mellin and Stieltjes holomorphy, all four integration-by-parts
statements and both Ritt estimates. Three existing Fourier corollaries also become
independent of admissions. [ProofRound20261029b.json](ProofRound20261029b.json) records the
proofs and validation. The higher-order Haar statement is retained as admitted because
its separate derivative data need a compatibility hypothesis; the review explains the issue.

The [Chapter 1–2 follow-up of 2026-10-29](REVIEW.md#chapter-12-proof-round-2026-10-29)
removes **24 further admissions**: 15 in Chapter 1 and nine in Chapter 2, leaving **1,710**.
It proves inequalities, complex-analysis and spectral identities, exact Fourier transforms,
integration of asymptotic equivalents, Haar decay, a Mellin coefficient formula and an
oscillatory-sum bound. Its inventory and validation are in
[ProofRound20261029.json](ProofRound20261029.json). The
[preceding round](REVIEW.md#admission-proof-round-2026-10-28) removed 37 admissions and
freed four existing downstream theorems from admitted dependencies.

Remaining source admissions by area: Elementary 61, GeneralizedHypergeometric 110,
QHypergeometric 90, EllipticIntegrals 183, Theta 13, RiemannTheta 7, JacobiElliptic 32,
Weierstrass 35, BernoulliEuler 24, Zeta 46, Combinatorics 36, NumberTheory 36, Mathieu 140,
Lame 41, Spheroidal 33, Heun 26, Painleve 42, Coulomb 49, WignerSymbols 34, MatrixArgument 36,
CoalescingSaddles 35, AlgebraicAnalytic 223, AsymptoticApproximations 104, and 185 in the older
areas. The current axiom audit verifies all newly completed proofs using only the standard
Lean/Mathlib axioms. The DLMF cross-reference audit records 8,681 proved entries, 2,022 entries
that depend on admissions, and no nonstandard axiom dependencies. The review also records
statement qualifications that require attention before further proof work.
Counts in the dated development history describe their earlier scope.

The [parallel priority round](REVIEW.md#priority-proof-implementation-with-parallel-ownership-2026-10-24)
proved eight existing admissions and removed two downstream inverse-series dependencies.
The [Elementary proof round](REVIEW.md#chapters-4-16-and-17-acquisition-and-elementary-proofs-2026-10-24)
then proved 102 newly acquired admissions without changing their statements, reducing
Chapter 4 from 447 to 345. The new ledgers distinguish direct admissions, proofs
that inherit admissions, branch-dependent definitions, and corrected source formulas.

The [second parallel proof round](REVIEW.md#parallel-proofs-in-chapters-4-16-and-17-2026-10-24-second-round)
proves 134 further statements: 92 Elementary, 14 generalized hypergeometric and 28
q-hypergeometric. It also makes `genHG_entire` independent of the continuation
existence admission. The guarded function definition preserves the previous values
under that explicitly retained existence theorem.

The [third parallel proof round](REVIEW.md#parallel-proofs-in-chapters-4-16-and-17-2026-10-24-third-round)
removes 47 admissions: 28 Elementary, six generalized hypergeometric and 13
q-hypergeometric. It proves the six boundary logarithm series in natural order,
q-series holomorphy and product continuation, finite inversions and normalized
bilateral Dougall. Four false inverse-hyperbolic set acquisitions are corrected
and proved with compatible branches. Two remaining arctanh boundary acquisitions
still need natural-order statements; the ledger records the defect.

The [duplication review](REVIEW.md#duplication-and-reuse-review-2026-10-22) consolidates
repeated hypergeometric algebra, scalar-series arguments, Bessel symmetry, Legendre
boundary limits, integral holomorphy, and spherical-harmonic helpers. It also records
remaining consolidation candidates and the branch and parameter distinctions that prevent
indiscriminate identification of special functions. Not every admitted statement has been
checked for correctness; statements found to be false or weaker than intended are repaired
as they are reviewed.

## Dependencies and upstream reuse

The project uses Lean `v4.36.0-rc1`, Mathlib revision
`911003dd6dea5df215dff57f2717be762e11a6ca`, and TauCeti revision
`a049b4264d2cf4dbf4720796f844a3a3764914a5`.

The 18 October 2026 upgrade uses Mathlib's development head. TauCeti's own
Mathlib pin is 65 commits earlier; [TauCeti-4.36.patch](TauCeti-4.36.patch)
updates one renamed coercion lemma for this snapshot. The shared checkout
already has this patch. After a fresh dependency checkout, apply it before
building:

```sh
git -C .lake/packages/TauCeti apply "$PWD/TauCeti-4.36.patch"
```

Prefer **Mathlib, then TauCeti, then local code**, preserving theorem hypotheses and the
meaning of each special-function definition. Import the particular TauCeti module;
`import TauCeti` is not a library umbrella.

See [TauCetiReview.md](TauCetiReview.md) for checked reuse candidates and the review's limits,
and [CREDITS.md](CREDITS.md) for related-work credits. The first six adaptations are implemented, including proofs of
both Hermite Fourier eigenfunction identities and compact-support Parseval. A later
pass (2026-10-05) proved 35 further admissions in the Gamma and orthogonal-polynomial
chapters (see [TauCetiReview.md](TauCetiReview.md)). A further pass (2026-10-07)
repaired the Gamma sine integral and two finite
Kummer–Bessel statements, and proved all ten theorems in priority groups 1–4:
the two Kummer zero results, compact-support expansion and kernel orthogonality,
three Hermite integrals, and three parameter/Euler integrals. The project-wide pass
on 2026-10-08 proved the Whittaker M pole limit, the `q`-Gegenbauer classical limit,
and both Laguerre fractional integrals, and repaired a missing parameter bound in
the Whittaker W Bessel-K integral. The next priority pass proved the Jacobi fractional
integral, both Rodrigues formulas, Legendre orthogonality, the unweighted Laguerre
convolution, the regularized Kummer Laplace self-transform, and the closed Whittaker M
Laplace transform. It also established convergence of Tricomi's Laplace kernel in the
full stated region and its `b = a + 1` specialization. The continuation pass proved
the weighted Laguerre convolution, the Jacobi squared norm, and Gegenbauer
orthogonality. Supporting lemmas now give the general Kummer transform when
`‖k‖ < Re z` and Tricomi's Laplace representation for every `b = a + N + 1`,
with nonnegative integer `N`. The full half-plane Kummer transform is now proved
using a polynomial exponential growth bound and holomorphic continuation, with
all denominator parameters retained. Tricomi's full Laplace representation is now
proved by a Gauss confluence limit, holomorphic continuation in the argument,
and continuity in the second parameter, including integer parameters. The
Whittaker W Laplace representation follows by an affine substitution. These
complete the remaining integral priorities without changing their statements.
Tricomi's Mellin transform is also proved throughout its original convergence
strip, with a separate absolute-integrability theorem. A Gamma pass on 2026-10-15,
guided by Temme's *Special Functions* (Wiley, 1996), Chapter 3, proved 24 further
admissions: Binet's three formulas for `log Γ`, the remaining digamma and
Euler-constant integrals of DLMF §5.9, Prym's and the Cauchy–Saalschütz
representations, the oscillatory and Fresnel-type Gamma integrals, derivatives and
integrals of `Γ` in its argument, Stirling's series for `log Γ`, `ψ` and `ψ⁽ⁿ⁾`, the
modulus and balanced Gamma products, and four Gamma inequalities. It also corrected
the bracketing of `Gamma_incomplete_sum`. A confluent pass, following Temme's Chapter 7,
derived Tricomi's and Kummer's asymptotic expansions from Watson's lemma (proving six
admissions in `DLMF.Confluent.Asymptotics`) and added admission-free modules for the
incomplete Gamma functions, the exponential, sine and cosine integrals, parabolic cylinder
functions, the Fresnel and Dawson integrals, and Coulomb wave functions. A further pass on
Temme's §§6.8–6.9 proved Laplace's integral for Legendre polynomials and added modules on
Legendre bounds, expansions and large-degree asymptotics and on Chebyshev expansions. Laplace's
integral for Gegenbauer polynomials and the exponential generating function of Legendre
polynomials are now proved. Tricomi's expansion is extended to complex sectors
`|arg z| ≤ π - ε`, which gives the asymptotics of the auxiliary Fresnel functions and of the
Coulomb functions `H^±`. The connection formula 13.2.41 and the Wronskians derived from it
(13.2.24–13.2.25, 13.2.35, 13.2.37–13.2.38) are proved. These give the irregular Coulomb
function `G_ℓ`, `H^±_ℓ = G_ℓ ± iF_ℓ`, the Coulomb Wronskian and the limits `F_ℓ ~ sin θ_ℓ`,
`G_ℓ ~ cos θ_ℓ`. Bounds for `Γ` on vertical lines and Mellin inversion give the Barnes
integrals for `₂F₁`, `𝐌`, `U`, `W` and AAR Theorem 4.2.1. The two-sided expansion 13.7.2 and the
Whittaker connection formula are proved. New results include the loop integral 15.6.2 and the
generalized hypergeometric equation. There are
now 1,008 remaining source admissions (2026-10-19), including 363 in Airy and
528 from the Chapters 6–8 acquisition described below. The first prioritized batch
removed 11 admissions: the Laguerre and Hermite Mehler–Heine limits, Laguerre–Bessel
integral and uniform bound, three monic moment determinant identities, disk-polynomial
polar formula, ball Poisson representation, and the `SU(2) → SO(3)` double cover.
The next finite-identity batch removed eight more admissions: two finite Kummer–Bessel
expansions, the Kummer and Whittaker products, three Gegenbauer expansion/connection/
linearization formulas, and the general Jacobi connection formula.
Five Whittaker transform statements now use regularized `M` at exceptional parameters;
the Mellin formula is proved, while the cosine and three Bessel formulas remain admitted. See [REVIEW.md](REVIEW.md#finite-identities-priority-batch-2026-10-18)
for the completed batches and validation. The
[further-priorities review](REVIEW.md#further-admission-priorities-2026-10-19)
describes the proof routes. The
[six-proof integral and orthogonality batch](REVIEW.md#six-proof-integral-and-orthogonality-batch-2026-10-19)
implements those targets: the adjacent Jacobi generating function, three Laguerre/Jacobi
integral formulas, finite Bessel-polynomial orthogonality, and Morse orthogonality.
The following [endpoint-limit and multivariate batch](REVIEW.md#jacobi-endpoint-limit-and-multivariate-orthogonality-2026-10-19)
proves Jacobi Mehler–Heine and disk and triangle orthogonality, completing the
remaining admissions in `Limits.lean` and `Multivariate.lean`.
The next [generating-function and Legendre batch](REVIEW.md#generating-functions-and-legendre-identities-2026-10-19)
proves the continuous Hahn, continuous dual Hahn and Wilson generating functions,
Legendre addition, and its product and singular integrals. All six original
statements and parameter ranges are retained.
The [confluent and Hermite batch](REVIEW.md#confluent-additions-boundary-transforms-and-mehler-2026-10-19)
proves all eight remaining Kummer/Whittaker first-parameter addition formulas,
the regularized Kummer and Whittaker Mellin transforms, and Mehler's formula.
A separate sharp Gamma-ratio bound for natural shifts is also proved. The two
Gamma and two Bessel admissions remain; the review records their proof dependencies
and the next analytic and polynomial targets.
The [Tricomi and continuous Hahn batch](REVIEW.md#tricomi-laplace-transforms-and-continuous-hahn-orthogonality-2026-10-19)
proves the remaining Tricomi/Whittaker Laplace transform pair and continuous Hahn
orthogonality. The transform proof lowers the unrestricted first parameter by
contiguous relations; the polynomial proof uses Barnes moments and
Pfaff–Saalschutz.
The [integer-parameter Tricomi batch](REVIEW.md#integer-parameter-tricomi-expansion-and-logarithmic-remainders-2026-10-19)
proves the logarithmic expansion at positive integer second parameter and the
small-argument bounds at `b=1`, `b=2`, and `b=0`. The two remaining basic U bounds
and the Jacobi generating functions are the next priorities.

The [Airy acquisition](AiryAcquisition.md) now covers every numbered equation in
DLMF §§9.2 and 9.4–9.14, together with the mathematical prose and numerical
tables. Fifteen new modules acquire 399 admitted statements; 36 are already
proved, including the rotated Wronskians, product equation and Wronskian,
antiderivative formulas and the general Airy solution. The 363 remaining Airy
admissions are listed with branches, convergence conventions, a qualification
for positive-parameter Reid ray integrals and the next proof priorities.

The [Chapters 6–8 acquisition](DLMF678Acquisition.md) covers all 468 active
numbered equations, explicit mathematical prose and numerical tables, excluding
graphs and application notes. Thirty new modules provide the expanded theory;
Mathlib results have comments and precise pointers. Of 547 initially admitted
statements, 187 are now proved and 360 remain. The inventory records branch and
convergence conventions and a proved counterexample to the unqualified Beta
continued-fraction bound following 8.17.23. The entry modules are
[ExpIntegrals](DLMF/ExpIntegrals.lean), [ErrorFunctions](DLMF/ErrorFunctions.lean)
and [IncompleteGamma](DLMF/IncompleteGamma.lean).

The [Chapters 11, 12 and 14 acquisition](DLMF111214Acquisition.md) adds Struve,
Lommel and Anger–Weber theory, expanded parabolic-cylinder theory and associated
Legendre/Ferrers, conical, toroidal and spherical-harmonic theory. Forty-four new
modules supply 198 definitions and 626 initially admitted statements; 110 are now
proved and 516 remain. The ledger accounts for all 601 selected numbered equations,
excluding graphs and application notes, with Mathlib pointers instead of duplicate
proofs. It records proved counterexamples to 12.13.6 and the left-cut zero rule in
§14.27, and explicitly lists domain extensions still to acquire. The entry modules
are [Struve](DLMF/Struve.lean), [ParabolicCylinder](DLMF/ParabolicCylinder.lean) and
[Legendre](DLMF/Legendre.lean). The project now has 1,356 explicit admissions;
the completed public proofs have no dependencies on them.

The [admission reuse review](REVIEW.md#reuse-of-the-proved-special-function-core-2026-10-19)
prioritizes incomplete-Gamma and exponential-integral specializations, error/Fresnel
bridges, incomplete-Beta recurrences, cylinder identities, associated Legendre theory
and regularized Struve series. It names an initial batch of 18 targets, distinguishes proved general
results from admitted prerequisites, and flags a sign transcription error in an
acquired Airy inverse-Bessel formula. The review itself changes no proofs.

The [seven-track proof batch](REVIEW.md#seven-track-admission-removal-2026-10-19)
removes 100 admissions: Gamma/exponential-integral core 24, error/Dawson/Fresnel 20,
Ein/E1/Si/Ci 24, incomplete Beta 5, cylinders/Weber 10, associated Legendre 12,
and Struve/Lommel 5. This includes the complex E1–Ein identity at every nonzero
argument, all-parameter continued-Gamma shifts, the associated-P equation,
and regularized 1F2 bridges for Struve and small Lommel. No existing statement,
assumption or definition was changed. The full build, 31 direct file checks and
an exact axiom audit pass; all new completed proofs are independent of admissions.
The remaining obligations and complete theorem inventory are in the review.

The [four-priority follow-up](REVIEW.md#four-priority-admission-removal-2026-10-20)
removes a further **69 admissions**, bringing the total to **1,440**. It proves 30
exponential-integral/error/Fresnel relations, 14 repeated-erfc/cylinder identities,
12 incomplete-Beta recurrences, limits and series, and 13 incomplete-Gamma shifts,
weighted derivatives and transforms. The original domains, exceptional parameters,
branches and definitions are preserved. The exact compiled dependency audit confirms
that all these proofs are independent of admissions; the full build and 19 direct
file checks pass. The review lists the completed theorems and remaining work.

The [Struve/Lommel forcing batch](REVIEW.md#struve-and-lommel-forcing-2026-10-20)
removes **15 more admissions**, leaving **1,425**. It proves the four Struve
equations with their forcing terms, five ordinary general-solution formulas,
two logarithmic continuation formulas, the small-Lommel equation and general
solution, and two Fresnel squared-norm identities. The new regularized `₁F₂`
equation retains reciprocal-Gamma zeros at exceptional parameters. The build,
10 direct checks and exact compiled axiom audit pass. The
[next-priorities review](REVIEW.md#next-proof-priorities-after-the-forcing-batch)
identifies the next transfers and their prerequisites.

## Supporting library `DLMFMathlib`

General results that the special-function library uses, following Temme's *Special
Functions* (Wiley, 1996), Chapters 1–2, and written for eventual contribution to Mathlib:

* `DLMFMathlib.NumberTheory.EulerPolynomials`: Euler polynomials and numbers, the difference
  equation `Eₙ(x+1) + Eₙ(x) = 2xⁿ`, the Appell property, reflection, alternating power sums,
  and the Euler-number recurrence.
* `DLMFMathlib.Analysis.EulerMaclaurin`: the Euler–Maclaurin formula with remainder.
* `DLMFMathlib.Analysis.BooleSummation`: Boole's alternating summation formula.
* `DLMFMathlib.Analysis.Asymptotics.AsymptoticExpansion` and `.Watson`: Poincaré asymptotic
  expansions and Watson's lemma, also with a complex exponent. In `DLMF.Gamma.Asymptotics`
  they give Stirling's series for `log Γ` as an asymptotic expansion
  (`hasAsymptoticExpansion_log_Gamma`); in `DLMF.Confluent` they give the expansions of
  Tricomi's and Kummer's functions and of the functions derived from them.
* `DLMFMathlib.Analysis.Asymptotics.WatsonSector`: Watson's lemma for complex `z → ∞` in a
  sector `δ|z| ≤ re z`, and the Gamma integral `∫₀^∞ u^{s-1} e^{-zu} du = Γ(s) z^{-s}`.
* `DLMFMathlib.Analysis.Complex.RotateRay`: rotation of a ray integral `∫₀^∞ f` to the ray
  `arg t = α`, from Cauchy's theorem for rectangles.
* `ToMathlib.Analysis.Integral.Laplace` (from the lean-codes dependency): quantitative
  Laplace asymptotics, re-exported by `DLMFMathlib.lean`.

`DLMFMathlib` (formerly `ToMathlib`, renamed 2026-10-25) imports Mathlib and lean-codes'
`ToMathlib` only and contains no admissions.

## Building

Run `lake build` from the repository root. The existing `.lake` symlink to the
local-disk cache is intentional and must not be replaced or retargeted.

Build outputs remain in `.lake/build-DLMF`, separate from companion projects.


The [four-track identity batch](REVIEW.md#four-track-identity-proofs-2026-10-20)
removes **58 admissions**, leaving **1,367**: 28 Struve, 17 incomplete-Gamma and
generalized-trigonometric, seven Legendre and six error-function results. It
completes the targeted Struve calculus, both modified solution formulas, the
negative half-integer families and eight elementary values; the short Gamma
transfers, including inherited-logarithm square identities; six Legendre degree
recurrences and the Olver-Q equation; and the repeated-erfc, Faddeeva and Fresnel
series transfers. All existing statements and definitions are preserved. The
full build, 26 direct checks and exact compiled axiom audit pass. The review
lists the remaining finite Struve sums and Ferrers-Q foundations explicitly.


The [finite-sum and Ferrers follow-up](REVIEW.md#finite-struve-sums-and-ferrers-foundations-2026-10-20)
removes **11 further admissions**, leaving **1,356**. It proves both remaining
Struve finite half-integer sums, all four targeted P order recurrences, the
Ferrers P/W₁/W₂ connection, the Ferrers-Q differential equation, lower-Gamma
parameter analyticity and logarithmic monodromy, and the generalized lower
trigonometric/Gamma bridge. A regularized quadratic connection extends through
exceptional lower parameters using the proved parameter-curve analyticity API.
The full build, 17 direct checks and exact compiled axiom audit pass. The
remaining Ferrers-Q connection/limit and Gamma complement/convergence work is
listed in the review.
