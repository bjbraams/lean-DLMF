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

| Area | AAR chapters | DLMF chapters | Submodules |
| --- | --- | --- | --- |
| `Gamma` | 1 | 5 | 23 |
| `Hypergeometric` | 2–3 | 15 | 20 |
| `Confluent` | 4.1–4.4 | 13 | 17 |
| `Bessel` | 4.5–4.15 | 10 | 14 |
| `Airy` | (Beals–Wong 9.9) | 9 | 17 |
| `Legendre` | (Temme 8) | 14 | 31 |
| `Statistical` | (Temme 11) | 7–8 | 3 |
| `Elliptic` | (Temme 12) | 19, 20, 22 | 4 |
| `WaveEquation` | (Temme 10) | | 1 |
| `Polylog` | (Duverney 8) | 25 | 3 |
| `Constants` | (Duverney 2, 8) | 25 | 3 |
| `OrthogonalPolynomials` | 5–7 | 18 | 18 |
| `Selberg` | 8 | | 2 |
| `SphericalHarmonics` | 9 | | 2 |
| `QSeries` | 10 | | 2 |
| `Partitions` | 11 | | single file |
| `Bailey` | 12 | | single file |

`DLMF.lean` imports all areas.

The additional DLMF chapter entry points include `Struve` (eight submodules) and
`ParabolicCylinder` (twelve submodules), extending the original cylinder API in
`Confluent`. Their acquisition status is recorded below.

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

DLMF errata and source corrections found anywhere in the project are collected in
[DLMFErrata.md](DLMFErrata.md): genuine DLMF errata, fixed transcription defects of our own,
and formalization notes, each with evidence and the Lean declarations.

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

| Function (DLMF) | Lean name | Miller macro |
| --- | --- | --- |
| Kummer `M(a,b,z)`, `U(a,b,z)` (13.2) | `kummerM`, `kummerU` | `KummerconfhyperM`, `KummerconfhyperU` |
| Whittaker `M_{κ,μ}`, `W_{κ,μ}` (13.14) | `whittakerM`, `whittakerW` | `WhittakerconfhyperM`, `…W` |
| Hankel `H^{(1)}_ν`, `H^{(2)}_ν` (10.4) | `hankelH1`, `hankelH2` | `HankelH1`, `HankelH2` |
| Modified Bessel `I_ν`, `K_ν` (10.25) | `besselI`, `besselK` | `modBesselI`, `modBesselK` |
| Legendre `P_ν`, `Q_ν` (14.3) | `legendreP`, `legendreQ` | `assLegendreP`, `assLegendreQ` |
| Ferrers `𝖯_ν^μ` (14.3) | `ferrersP` | `FerrersP` |
| Classical OPs (18.3) | `jacobiPolyP`, `ultrasphPoly`, `legendrePolyP`, `laguerrePolyL`, `hermitePolyH` | `JacobipolyP`, …, `HermitepolyH` |
| `γ(a,z)`, `Γ(a,z)` (8.2) | `lowerIncGamma`, `upperIncGamma` | `incgamma`, `incGamma` |
| `P(a,z)`, `Q(a,z)`, `γ*(a,z)` (8.2) | `normIncGammaP`, `normIncGammaQ`, `scIncGamma` | `normincGammaP`, `…Q`, `scincgamma` |
| `B_x(a,b)`, `I_x(a,b)` (8.17) | `Real.incBeta`, `Real.normIncBetaI` | `incBeta`, `normincBetaI` |
| `erf`, `erfc`, Dawson `F` (7.2) | `erf`, `erfc`, `Real.dawsonF` | `erf`, `erfc`, `DawsonintF` |
| Fresnel `C`, `S` (7.2) | `Real.fresnelCosInt`, `Real.fresnelSinInt` | `Fresnelcosint`, `Fresnelsinint` |
| `Si`, `Ci`, `Cin`, `Ein`, `E_p` (6.2, 8.19) | `Real.sinInt`, `Real.cosInt`, `Real.cosIntCin`, `Real.expIntEin`, `genExpIntE` | `sinint`, `cosint`, `cosintCin`, `expintEin`, `genexpintE` |
| `Li_s`, `Li₂`, `Li₃` (25.12) | `polylogSeries`, `Real.dilog`, `Real.trilog` | `polylog`, `dilog` |
| Barnes `G`, `ψ^{(n)}`, `Γ_q`, `B_q`, `[n k]_q` | `barnesG`, `polygamma`, `qGamma`, `qBeta`, `qBinom` | `BarnesG`, `polygamma`, `qGamma`, `qBeta`, `qbinom` |
| `K`, `E`, `Π`, `D` complete (19.2.8) | `compEllIntKk`/`…Km`, `compEllIntEk`/`…Em`, `compEllIntPik`/`…Pim`, `compEllIntDk`/`…Dm`; now `compEllIntKkSeries`, `Real.compEllIntKm`, `Real.compEllIntEm`, `Real.compEllIntPim` | `compellintKk`, `compellintEk`, `compellintPik`, `compellintDk` |
| `F(φ,k)`, `E(φ,k)`, `Π(φ,α²,k)` (19.2.4–7) | `incEllIntFk`/`…Fm`, `incEllIntEk`/`…Em`, `incEllIntPik`/`…Pim`; now `Real.incEllIntFm`, `Real.incEllIntEm`, `Real.incEllIntPim` | `incellintFk`, `incellintEk`, `incellintPik` |
| `K′`, `E′` (19.2.9) | `ccompEllIntKk`, `ccompEllIntEk` (planned) | `ccompellintKk`, `ccompellintEk` |
| `am`, `sn`, `cn`, `dn`, `arcsn` (22.2, 22.15, 22.16) | complex `DLMF.JacobiElliptic.jacobiSnk`, … (all twelve) and `jacobiSnTau`, …; real `Real.jacobiAmm`, `Real.jacobiSnm`, `Real.jacobiCnm`, `Real.jacobiDnm`, `Real.jacobiArcsnm` | `Jacobiamk`, `Jacobiellsnk`, …, `aJacobiellsnk` |
| `θ_j(z\|τ)`, `θ_j(z,q)`, `θ_j(q)` (20.2) | `jacobiThetaOneTau`, …, `jacobiThetaFourTau`; `DLMF.Theta.jacobiThetaOneQ`, …; `Real.jacobiThetaThreeNullQ`, `Real.jacobiThetaFourNullQ` | `Jacobithetatau`, `Jacobithetaq` |
| Carlson `R_F`, `R_D`, `R_C`, `R_J`, `R_G` (19.16) | `carlsonRF`, … (planned) | `CarsonsymellintRF`, … (sic) |

The real digamma function is still `Real.digamma`, defined in Mathlib's `Real` namespace beside
Mathlib's `Complex.digamma`; moving it into `DLMF.Gamma.Real` is left for a later pass.

## Status

After the fourth Chapter 4/16/17 proof round (2026-10-24) and the Chapters 19–23
acquisitions (2026-10-25) there are **1,173 explicit source admissions**: Elementary 68,
GeneralizedHypergeometric 112, QHypergeometric 101, EllipticIntegrals 281, Theta 74,
RiemannTheta 10, JacobiElliptic 215, Weierstrass 123, and 189 in the older areas. The compiled
audit finds **16,253 project theorems**, with **1,328 depending transitively on `sorryAx`**, and no
other nonstandard axiom.
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
`5cdecf40e99d5a5ad0833afff31f5b007d68a149`, matching the companion projects.

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
