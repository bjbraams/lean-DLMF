# Mathlib-style review of lean-DLMF, 2026-10-30

Implementation follow-up: [statement corrections and shared-API cleanup](REVIEW.md#review-cleanup-statement-corrections-and-shared-apis-2026-10-30).
The findings and counts below describe the pre-cleanup state.

Reviewed commit: `3989f9ed5aaac53a742d6ba239deeb32708c9b60`.
The library builds and its foundational import layer passes the current policy checks.
It still needs substantial API cleanup before it would resemble a collection of Mathlib
contributions. The most valuable work is to correct the known statement problems, weaken
unnecessary hypotheses, consolidate shared definitions and proofs, and replace development
round names with mathematical names. Missing formal docstrings and files over 1,500 lines
are no longer outstanding library-wide problems.

This is a review, with experiments in temporary files; no library declarations, statements,
proofs or imports were changed. The accompanying
[inventory](MathlibReviewInventory20261030.json) records file hashes, findings, the complete
candidate lists, and the audit programs and Lean experiments. Earlier reviews in
[REVIEW.md](REVIEW.md) are historical snapshots, not the measurements for this review.

## Coverage and evidence

The source scan covers all 1,199 library files under `DLMF/`, `DLMFMathlib/` and the two
library roots: 540,486 physical lines. It identifies 26,262 explicit named declarations:
17,852 `theorem`, 4,926 `lemma`, 3,362 `def`, 52 `abbrev`, 55 `structure`, seven `inductive`
and eight named `instance` declarations. There are also 14 anonymous instances, audited
separately. These counts exclude compiler-generated recursors, projections and auxiliary
declarations; `theorem` and `lemma` are different source spellings of the same Lean concept.

All 26,262 named declarations were matched to compiled declarations by module, name and
source range. Documentation, result sorts, exact expression comparisons and axiom
dependencies were checked in the compiled environment. Direct admissions remain at 1,553;
1,655 of the source theorem/lemma declarations depend on `sorryAx`, including indirect
dependencies. The latter were excluded from the removable-hypothesis audit.

Automated checks cover the whole library. Mathematical reading concentrated on the
foundations, general analysis and combinatorics APIs, the largest proofs, repeated proof
families, exact upstream matches and previously flagged formulations, with examples across
the special-function areas. This is not a certification that every one of the 22,778
theorem/lemma statements is maximally general. The inventory distinguishes verified
expression-level findings from naming and refactoring candidates.

The comparison uses the pinned dependencies: Mathlib
`911003dd6dea5df215dff57f2717be762e11a6ca`, TauCeti
`a049b4264d2cf4dbf4720796f844a3a3764914a5`, and the existing lean-codes path dependency,
with Lean `v4.36.0-rc1`. The review follows the official
[naming](https://leanprover-community.github.io/contribute/naming.html),
[documentation](https://leanprover-community.github.io/contribute/doc.html) and
[style](https://leanprover-community.github.io/contribute/style.html) guides. In particular,
names should describe the mathematics, proof names normally use snake case, type and
predicate names use upper camel case, and data definitions use lower camel case.
Embedded names of existing objects retain their spelling.

## 1. Correct statement problems before further proof work

The following previously identified problems are still present in the current sources.
An admission is not itself a statement defect, but these formulations need attention
independently of proving them. The detailed evidence and distinction between DLMF errata
and acquisition mistakes are in [reports/DLMFErrata.tex](reports/DLMFErrata.tex).

- [prod_mtest_log](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L502) concludes global
  uniform convergence from bounds on a tail of the logarithms. An uncontrolled finite
  prefix can be unbounded on the domain. Taking the first factor to be `exp z` and a
  nonconstant converging sequence of constant tail products defeats global uniform
  convergence on the whole plane. Use local uniform convergence, or add an appropriate
  bounded-prefix condition. The related all-factor bound in `prod_mtest` is a different
  situation and should not be weakened indiscriminately.
- [hasCesaroSumOfOrder_of_tendsto](DLMF/AlgebraicAnalytic/Summability/Series.lean#L75)
  assumes only `-1 < α`. Regularity fails for negative orders. The recorded example uses
  order `-1/2` and terms `(-1)^n (1/2)_n/n!`. State the regularity theorem for nonnegative
  order, with the zero-order case handled explicitly.
- [picard_great](DLMF/AlgebraicAnalytic/Complex/Functions.lean#L123) needs a positive outer
  radius. At radius zero the punctured-disc analyticity hypothesis is vacuous; complex
  conjugation supplies a counterexample. This is an acquisition issue, not an error in
  the classical theorem.
- [liouvilleGreen_interval_isEquivalent](DLMF/AsymptoticApproximations/ODE/LiouvilleGreen.lean#L126)
  includes uniqueness at regular finite endpoints. For `f = 1`, `g = 0`, `ξ(x) = x` on
  `(0,1)`, both `exp x` and `exp x + sinh x` have the required equivalence at zero.
  Separate existence and error estimates from uniqueness, and carry the required singular
  endpoint assumptions into the uniqueness result. The declaration's docstring already
  acknowledges the problem; the statement is still unchanged.
- The three shifted-theta formulas
  [jacobiThetaTwoTau_powerSeries](DLMF/Theta/PowerSeries.lean#L78),
  [jacobiThetaThreeTau_powerSeries](DLMF/Theta/PowerSeries.lean#L88) and
  [jacobiThetaFourTau_powerSeries](DLMF/Theta/PowerSeries.lean#L98) use the unshifted
  lattice radius. They require the corresponding shifted zero-lattice distances.
  At `τ = I` the present discs contain zeros of their left sides, whereas their claimed
  exponential expressions are nonzero. Existing proof-round records contain Lean-checked
  counterexamples. Do not keep the same radius merely to give these four formulas a
  uniform interface.
- [symEllIntR_half_hasSum_mean](DLMF/EllipticIntegrals/SymmetricSeries.lean#L269) needs
  additional branch compatibility: the mean being in the slit plane and the normalized
  deviations having norm less than one do not suffice. There is a recorded exact Lean
  counterexample. Repair the homogeneity/branch hypotheses before attempting the sum.
- [symEllIntRC_sq_eq](DLMF/EllipticIntegrals/SymmetricAddition.lean#L730) allows
  `x = -I`, `y = 1`, which is incompatible with the claimed principal-value identity.
  The first squared argument is then outside the relevant DLMF domain. This is a problem
  with the acquired extension of the formula; do not report this example as a DLMF erratum.

Two further hypothesis questions remain open, rather than established counterexamples to
the full statements: the derivative-existence assumptions in
[the variable-limit and improper Leibniz rules](DLMF/AlgebraicAnalytic/Calculus/SeveralVariables.lean#L372),
and the separate derivative data in
[haar_isLittleO_pow](DLMF/AsymptoticApproximations/Integrals/Watson.lean#L398).
Continuity of a totalized `deriv` expression does not assert differentiability, and
holomorphy of `Q - F` does not by itself identify the separate totalized derivatives with
derivatives of that difference. Supply the missing mathematical argument or explicit
existence/compatibility assumptions. The report does not classify these pending questions
as proved false.

## 2. Generality and hypotheses

### Kernel-verified removable binders

There are **341 removable binders in 291 admission-free theorems**; 334 binders belong to
286 public theorems. Each candidate was absent from both the remaining type and the
elaborated proof. For every candidate, I removed that binder, adjusted bound-variable
indices, and checked the resulting proof and type with Lean's kernel. These checks remove
binders individually, not all binders in a declaration simultaneously. The inventory gives
every name, binder, source location and narrowed type.

Examples with a clear API benefit:

- [jacobi_at_one](DLMF/OrthogonalPolynomials/Explicit.lean#L272) does not need
  `-1 < α.re`: its proof is `simp [jacobiPolyP]`. The evaluation holds for every complex
  `α, β`. Keep the positivity-type hypothesis on the subsequent nonvanishing theorem,
  where it serves a real purpose. Rename the general evaluation `jacobiPolyP_one`.
- [whittakerW_laguerrePolyL](DLMF/Confluent/Relations.lean#L1151) does not need its
  `z ∈ slitPlane` hypothesis. The denominator regularity hypothesis remains a separate
  matter; the audit does not remove it.
- [tendsto_contourIntegral_tsum](DLMF/AlgebraicAnalytic/Complex/Calculus.lean#L1023)
  does not need `_hD : IsOpen D`.
- [integrableOn_powKernel_mul_rpow_iff](DLMF/AsymptoticApproximations/Distributional/FractionalIntegrals.lean#L45)
  does not need `_hα1 : α ≤ 1`.
- [airy_ai_real_error](DLMF/Airy/Asymptotics/RealRemainders.lean#L489) includes the
  automatic fact `0 ≤ N` for a natural number `N`. Similar occurrences appear in the
  other Airy remainder interfaces.
- [integral_eq_integral_Ioi_add_neg](DLMFMathlib/MeasureTheory/Integral/HalfLine.lean#L26)
  carries an unnecessary completeness binder. More redundant typeclass binders occur in
  the Watson-sector and parametric-holomorphy APIs. Remove the audited binder, checking
  the entire elaborated signature; do not infer that every surrounding theorem can
  discard completeness.

Some findings are deliberate compatibility wrappers: for example,
[besselJ_infinite_zeros](DLMF/Bessel/Asymptotics.lean#L588) explicitly points to the
stronger `besselJ_infinite_zeros_of_real`. Such wrappers are not new mathematical problems.
Prefer the stronger theorem at call sites; retain a documented compatibility alias only
when it serves a migration purpose. Prefixing an unused hypothesis with `_` silences a
warning but does not improve the interface.

### Hypotheses that follow mathematically from the others

The syntactic audit deliberately misses assumptions that a proof uses but could derive.
Three additional simplifications were proved in strict Lean experiments, with only
`propext`, `Classical.choice` and `Quot.sound` as axioms:

1. In [hasSum_primitive_monomials](DLMF/Core/Framework.lean#L73), `hb` follows from `hs`.
   Apply `(hs (R : ℂ)).summable.norm` and simplify the norm for `R ≥ 0`. The theorem should
   accept the global `HasSum` hypothesis alone. A separate theorem with local domination
   assumptions could still be useful when a series is known only on a disc.
2. In [Complex.mul_integral_comp_mul_eq_sub](DLMFMathlib/Analysis/Complex/SegmentPrimitive.lean#L68),
   the hypothesis `∀ z, HasDerivAt g (f z) z` already implies continuity of `f`:
   `g` is entire, `f = deriv g`, and Mathlib's `Differentiable.deriv` makes that derivative
   entire. Remove the independent `Continuous f` hypothesis here and in the two adapters
   [primitive_eq_sub and segmentIntegral_eq_sub](DLMF/Core/Framework.lean#L56).
   This argument uses complex holomorphy; it should not be transferred to arbitrary real
   differentiable functions.
3. [r27_absEval](DLMFMathlib/RingTheory/PowerSeriesEvaluation.lean#L31) is equivalent to its
   `HasSum` conjunct alone. For complex-valued terms, that conjunct already implies the
   norm summability conjunct. The explicit equivalence compiles. Simplify this predicate
   and its API, or justify a more general target where the two properties differ.

### Appropriate generalization

The general asymptotic-expansion framework is already a good model:
[AsymptoticExpansion.lean](DLMFMathlib/Analysis/Asymptotics/AsymptoticExpansion.lean)
uses an arbitrary filter, a normed scalar field and vector coefficients. The finite-sum
transport helpers also often use `AddCommMonoid` rather than concrete scalars.

The following are useful next generalizations, not claimed completed changes:

- The half-line integral convergence predicates in
  [Core/Framework.lean](DLMF/Core/Framework.lean#L32) can use an appropriate normed real
  vector-space target instead of being restricted to `ℂ`. Their limit conventions should
  stay explicit: convergence of finite integrals is not synonymous with absolute
  Bochner integrability on the infinite interval.
- General series-evaluation algebra in `R27PowerSeriesEval.lean` should be considered over
  a suitable complete normed ring, with a coefficient homomorphism where useful. First
  remove the redundant complex-specific predicate data; do not generalize an unnecessarily
  complicated interface.
- Algebraic identities inside Jacobi cyclic proofs can be stated independently of the
  special functions, over a field with the actual needed nonzero denominators. This makes
  both their assumptions and their reuse clearer.

There is no general recommendation to replace complex special functions by arbitrary
scalar-valued functions. Principal branches, Gamma poles, exceptional hypergeometric
parameters and the real symmetric matrix cone are mathematically meaningful restrictions.
In particular, `genSeriesConvergesTo` intentionally represents natural-order convergence,
including conditional convergence; replacing it with `HasSum` would change its meaning.

## 3. Upstream reuse and local duplication

### Exact upstream matches

Eighty source theorems have a type exactly equal to an upstream theorem type in the loaded
environment. Sixty-two have at least one accessible public upstream match; the remaining
18 match only private declarations and are not direct reuse opportunities. The 54 distinct
upstream declarations involved have been axiom-audited: none depends on an admission or
nonstandard axiom. Exact types were compared as expressions, not merely by hash.

This is a conservative search: it misses stronger upstream results, reordered binders,
equivalent formulations and changes of notation. Conversely, an exact match need not be
a copied proof: some local declarations are already one-line adapters. The inventory
contains the matches so these cases can be distinguished.

Concrete replacements or removals include:

- [DLMF.Zeta.riemannZeta_four](DLMF/Zeta/IntegerArguments.lean#L39) can use the existing
  root `riemannZeta_four`, rather than specialize the general Bernoulli formula again.
- [sin_int_mul_pi_complex](DLMF/Bessel/SecondKind.lean#L142) repeats
  `Complex.sin_int_mul_pi`.
- [DLMF.Gamma.integrable_exp_neg_mul_abs](DLMF/Gamma/VerticalBounds.lean#L309) repeats
  `TauCeti.integrable_exp_neg_mul_abs` with exactly the same type; its separate half-line
  proof can be removed after importing the specific upstream module.
- [Complex.ofReal_cpow_eq_exp_log_mul](DLMFMathlib/Analysis/SpecialFunctions/Pow/ComplexReal.lean#L28)
  repeats lean-codes' `Complex.ofReal_cpow_eq_exp`.
- The local positive-real square-root/power facts in Airy, Jacobi, Struve and elliptic
  integral files repeatedly match `Carlson.ofReal_cpow_half`, `Carlson.cpow_half_sq` and
  `Carlson.re_cpow_half_pos`. Reuse their common API rather than maintain parallel proofs.

Under the project's acquisition policy, a result already in Mathlib normally deserves a
precise upstream pointer rather than another local theorem solely for a DLMF tag. An
adapter remains useful for a genuinely different normalization or interface. The existing
explicit compatibility alias in
[Gamma/Simplex/GammaPochhammer.lean](DLMF/Gamma/Simplex/GammaPochhammer.lean) is already
documented as such; it should not be mistaken for a substantial duplicate proof.

### Identical definition bodies

There are 27 pairs of explicit public definitions with identical types and bodies.
Generated recursors are excluded. These are verified equal expressions, but deciding
whether to erase a mathematical name still requires judgment.

High-value consolidation candidates:

- [Airy/Framework.lean](DLMF/Airy/Framework.lean#L35) repeats the core `HasIntegralAtTop`,
  `HasIntegralAtBot`, `improperAtTop` and straight-segment integral. Use the core definitions
  and retain Airy-specific integral conventions only where they differ.
- The three identical raising operators `Hypergeometric.mulDerivMul`,
  `Hypergeometric.genRaiseOp` and `Confluent.mulDerivMul` live in three theorem files.
  Give the common operator one foundational home and one name.
- [LegendreWronskian](DLMF/Legendre/Associated/Wronskians.lean#L215) repeats
  `DLMF.Confluent.wronskian`. More generally the project has several Wronskian APIs.
  Consolidate equal normalizations; the weighted Sturm Wronskian and higher-order
  determinant are distinct constructions and should not be conflated.
- `periodicBernoulliB` duplicates `periodicBernoulli`, and `periodicEulerE` duplicates
  `antiperiodicEuler` in the general support layer. Preserve the endpoint convention when
  choosing the common API; the bridge to Mathlib's additive-circle function is useful.
- `Elementary.expPartialSum` and `Confluent.expPartialSum` have the same definition.
  `partitionCountAtMostParts` and `partitionsAtMost` likewise duplicate the same counting
  construction across areas.

Coincident cut domains for different inverse functions may deserve separate descriptive
names. Likewise distinct coefficient families can coincide by definition in a special
normalization. Those pairs are in the inventory, but are not automatic deletion requests.
For every consolidation, move the canonical definition down the import graph; do not
introduce a theorem-file dependency into `Basic/`.

## 4. Names, capitalization, visibility and namespaces

The main special-function names usually follow the expected lower-camel convention.
There remain substantial exceptions in auxiliary APIs:

- **76 public predicate definitions start with a lowercase letter.** Examples are
  `genDenRegular`, `genTerminates`, `genSeriesConvergesTo`, `qWellPoised`, `symEllIntArg`,
  `Complex.separatesPoleSets` and `Complex.hasVerticalTails`. Prefer names such as
  `GenDenRegular`, `GenTerminates`, `GenSeriesConvergesTo`, `QWellPoised`, `SymEllIntArg`,
  `SeparatesPoleSets` and `HasVerticalTails`, adjusting the surrounding API consistently.
  These are actual `Prop`-valued definitions, not theorem names.
- `LegendreWronskian` is a data-valued function and should not use type-style capitalization.
  Consolidating the Wronskian API is preferable to a cosmetic isolated rename.
- About 4,966 public names match a development-prefix heuristic, with families such as
  `p22R1_*`, `q27_*`, `s26a_*` and `je22a_*`. This count is a candidate inventory, not
  4,966 independently adjudicated violations. Source chapter numbers belong in docstrings
  and DLMF attributes; names should identify the operation, hypothesis or conclusion.
- Names such as `airy_ai_real_error` and `airy_aiDeriv_real_error` are inconsistent with
  the existing `airyAi`/`airyAiDeriv` vocabulary. Choose one vocabulary for the family.
  Where names like `jacobi_at_one` omit the actual function name, improve searchability
  with `jacobiPolyP_one` rather than preserving an informal abbreviation.

There are 25,382 public named declarations and 880 private ones. Many one-use algebraic
steps are exported through public sections. An API pass should make implementation details
private and promote genuinely reusable helpers under mathematical names. Visibility
changes require checking downstream uses; a small proof alone does not imply a theorem
should be private.

The `DLMF.<Area>` namespaces are reasonable project boundaries. Generic extensions in
`DLMFMathlib` should live in the existing upstream namespaces they extend. In particular,
the root-level `stRem_*` and `r27_*` APIs should receive mathematical namespaces and names.
The nested `DLMF.NumberTheory.DirichletCharacter.apply_ne_zero_iff` also illustrates the
distinction between adding a theorem to the existing `DirichletCharacter` namespace and
creating a new nested namespace accidentally or for historical compatibility.

The preservation of `DLMF.Confluent` names in the reorganized Coulomb and
parabolic-cylinder files is intentional compatibility, not a namespace error by itself.
Document and, eventually, migrate such interfaces as a coordinated change rather than
renaming them merely to match their file paths.

## 5. Documentation and modules

Every audited named library declaration and all 14 anonymous instances have a nonempty
formal docstring. All **205 directly declared structure fields** have formal docstrings.
Inherited parent subobjects and compiler-generated recursors are excluded from that field
count. No declaration docstring reduces to just its declaration name after stripping
punctuation and case. The user's documentation requirement is stronger than Mathlib's
baseline for every auxiliary lemma, and the project now meets its formal-presence part.

Semantic quality is less uniform:

- Some docstrings explain only a dependency, for example
  [ordinaryHypergeometricSeries_eq_binomialSeries_comp](DLMF/Hypergeometric/SeriesProperties.lean#L177)
  and [poch_three_halves_factorial](DLMF/OrthogonalPolynomials/Classical.lean#L763).
  State the series identification or factorial identity first; mention the consuming
  theorem second.
- There are 1,833 docstrings containing boilerplate such as “under the stated hypotheses”.
  Many include a useful formula and are acceptable for elementary identities. For major
  results, explain the mathematical role, branch and convergence convention instead of
  merely copying a long type into prose. This count is not a list of 1,833 defective docs.
- [Core/Framework.lean](DLMF/Core/Framework.lean#L20) still advertises only the Chapters
  6–8 acquisition, although it now serves the whole project and includes primitives,
  continued fractions, spherical functions and other support. Expand its scope description
  or split these topics into clearer modules.
- [DLMF.lean](DLMF.lean) has only a title as its module docstring. Its header should identify
  the complete-library entry point, direct readers to `DLMF.Basic`, and summarize the area
  organization. Similarly,
  [Painleve/Basic/Equations.lean](DLMF/Painleve/Basic/Equations.lean#L28) needs a short
  account of its solution predicates, differentiation convention and Bäcklund data;
  its title alone does not meet the requested scope summary.
- [ConnectionFormulas.lean](DLMF/Hypergeometric/ConnectionFormulas.lean#L14) says pole
  restrictions “can later be weakened”, but the reciprocal-Gamma companion already does
  that. Link the more general interface explicitly and describe the current relationship.

All 1,199 library files have `module` and a module docstring, placed before declarations.
The utility [scripts/DumpDLMF.lean](scripts/DumpDLMF.lean) lacks `module`; it is a separate
environment-dumping script, not a library module. There are no missing library module
headers. An inline module title is not by itself a missing-title error.

## 6. Long proofs and repeated proof fragments

There are **901 tactic proofs longer than 60 physical lines**, including 208 over 100.
Five of the 901 depend indirectly on admissions. These are review targets, not failures
of a hard proof-length rule. The inventory records every one. The longest observed tactic
proof has about 270 lines; most large files already use helper lemmas extensively.

The highest-value refactorings are:

1. [Hypergeometric/ConnectionFormulas.lean](DLMF/Hypergeometric/ConnectionFormulas.lean#L674)
   and [LogConnectionsRecipGamma.lean](DLMF/Hypergeometric/LogConnectionsRecipGamma.lean#L92)
   repeat parameter differentiation, termwise derivative convergence, finite/infinite
   splitting and algebraic reassembly. The major proofs are roughly 236–268 lines.
   Make the pole-free reciprocal-Gamma formulas the primary mathematical results and
   derive the restricted digamma versions when possible. Extract the common analytic
   differentiation and coefficient identities. The companion currently imports
   `ConnectionFormulas`, so this requires moving shared tools below both files; simply
   invoking the companion from the original file would create a cycle.
2. [JacobiElliptic/Cyclic/MixedTripleProducts.lean](DLMF/JacobiElliptic/Cyclic/MixedTripleProducts.lean#L33)
   has proofs of about 270 and 257 lines dominated by polynomial certificates. Separate
   evaluation of shifted Jacobi functions from the algebraic identity in their values.
   State the latter with its actual polynomial relations and denominator assumptions.
   Keep the special-function theorem short and mathematically readable. Moving an
   unchanged 200-line certificate into arbitrarily numbered pieces would not help.
3. [Mathieu/SmallQ.lean](DLMF/Mathieu/SmallQ.lean#L100) repeats residual and zero-row checks
   across 13 eigenvalue expansions. A finite-support trial-vector/residual interface, with
   a theorem that sufficiently remote rows vanish, should replace repeated branches.
   Keep the exact rational coefficient data explicit and auditable.
4. [JacobiElliptic/PeriodsPolesZeros.lean](DLMF/JacobiElliptic/PeriodsPolesZeros.lean#L210)
   repeats the same quarter-period composition argument for all 12 quotient functions.
   Prove the composition once for distinct numerator/denominator `JacobiLetter`s and
   specialize it. The file already has the relevant letter permutations and multipliers.
5. [Painleve/BacklundDLMF/Sixth.lean](DLMF/Painleve/BacklundDLMF/Sixth.lean#L472)
   has large quadratic and quartic-root transformations. Separate derivative transport,
   exclusion of poles/denominators, and verification of the transformed equation.
   These are meaningful reusable stages; algebraic endgame fragments alone are not.
6. The approximately 211- and 208-line construction proofs in
   [LiouvilleGreenFinite.lean](DLMFMathlib/Analysis/ODE/LiouvilleGreenFinite.lean#L387) and
   [LiouvilleGreenExpansion.lean](DLMFMathlib/Analysis/ODE/LiouvilleGreenExpansion.lean#L71)
   merit a shared Volterra-construction API. Retain the distinction between finite-endpoint
   normalization and a recessive condition at infinity: they are different uniqueness
   and error-control problems.

The exact-fragment scan found 495 repeated eight-line windows within files after partial
overlap suppression. This is not 495 independent duplicated proofs: some groups overlap
or describe necessary specializations. The highest-frequency families are the Mathieu
small-parameter expansions and Jacobi period/limit formulas above. Inspect these families
as a whole before creating helpers. Prefer a mathematical statement with a clear contract
to a lemma exposing a tactic-specific intermediate normal form.

## 7. File lengths, names and organization

No Lean file exceeds the 1,500-line limit. **134 library files exceed 1,000 lines.**
The largest are:

- `MatrixArgument/GammaBeta.lean`: 1,454 lines.
- `Spheroidal/Angular.lean`: 1,452.
- `Hypergeometric/ConnectionFormulas.lean`: 1,445.
- `Confluent/LargeA.lean`: 1,438.
- `Legendre/AdditionTools.lean`: 1,419.
- `Elementary/Trigonometric/InverseIdentities.lean`: 1,417.
- `QHypergeometric/BasicSummations.lean`: 1,412.
- `Legendre/Series.lean`: 1,408.

There is little room for growth in these files. Good prospective splits are:

- `MatrixArgument/LaplaceTransform.lean`, `GammaIntegrals.lean` and `BetaIntegrals.lean`,
  with Cholesky and cone-integral tools below their consumers and `GammaBeta.lean` as an
  umbrella. Its existing sections provide genuine mathematical boundaries.
- `Spheroidal/Angular/ElementaryProperties.lean`, `LegendreLimit.lean`, `PowerSeries.lean`,
  `Orthogonality.lean`, `SecondKind.lean` and `ComplexArgument.lean`, sharing lower-level
  coefficient tools rather than importing the whole angular theory into each other.
- Hypergeometric connection tools and pole-free formulas, following the proof dependency
  restructuring described above. Reduce duplicate proofs before deciding the final split.
- Q-hypergeometric summation helpers, terminating sums and nonterminating identities,
  moving the derivative/shift machinery into a common lower-level file when shared.

Do not split merely to reach an arbitrary line count below 1,000. Keep a coherent theorem
with its small supporting facts, and retain useful umbrella import paths.

Sixty file paths still contain development-round identifiers. For example, prefer
`Analysis/ODE/EntireLinear.lean` to `P1oEntireLinear.lean`,
`Analysis/ODE/ParametricHolomorphy.lean` to `P1oParamHolomorphic.lean`, and
`EllipticIntegrals/SymmetricIntegralBounds.lean` to `P19sR1Bounds.lean`.
Choose the mathematical scope first, then update imports and catalogues together.
The generic names `Tools`, `Helpers` and `Theorems` are acceptable temporary containers
but should be made more descriptive when their scope becomes stable.

The foundational reorganization is sound as an import layer: the survey finds no forbidden
foundation-to-theorem imports, missing modules or file cycles, and no new two-way area
pairs relative to the current baseline. The 16 existing two-way area pairs are allowed;
cycles in the area-level summary are not cycles in the file graph.

The foundation entry point is still not an exhaustive catalogue of mathematical
definitions. In particular, [EllipticIntegrals/Symmetric.lean](DLMF/EllipticIntegrals/Symmetric.lean)
defines the principal symmetric integrals but imports the theorem/support file
`P19sR1Bounds`; it is not exposed by a corresponding `EllipticIntegrals.Basic` entry point.
Move the canonical domain predicates and defining integrals into descriptive foundational
leaves, then put Carlson comparison theorems in a bridge file and add the foundation
umbrella to `DLMF.Basic`. This would make the high-level foundational view more complete
without copying definitions.

There is one policy ambiguity worth resolving explicitly: the support-layer description
in `AGENTS.md` says `DLMFMathlib` imports Mathlib and lean-codes only, while the general
policy allows TauCeti throughout. The existing
`DLMFMathlib/NumberTheory/T27aPrimeNumberTheorem.lean` directly imports TauCeti.
Its reuse is mathematically appropriate; clarify the documented exception or intended
support-layer rule rather than silently replacing that proof.

## 8. Routine style and import hygiene

The successful build still emits 1,468 warning headers unrelated to admissions:
610 unused simp arguments, 315 unused-tactic reports, 275 unused named variables,
131 never-executed tactic reports, 64 unnecessary-sequencing reports, 58 deprecations,
14 “simp already closes the goal” reports and one unused-section-variable report.
Some warnings concern the same proof step, so this is not 1,468 distinct mathematical
defects. Preserve the enabled linters and work through their suggestions after API changes.
In particular, a source-level unused-variable warning is weaker evidence than the
type-and-proof kernel audit above.

There are 4,376 source lines longer than 100 characters and 544 files with an unsorted
consecutive import block. Twenty files have runs of at least four blank lines, largely
left by moved declarations; `Hypergeometric/SeriesProperties.lean` has a 29-line run and
the Appell series file a 33-line run. These are straightforward cleanup candidates.
The official style guide recommends readable line lengths and ordered imports; formatting
should follow mathematical and dependency cleanup rather than obscure it.

A concrete import simplification was verified: a temporary copy of
[DLMFMathlib/Analysis/Complex/SegmentPrimitive.lean](DLMFMathlib/Analysis/Complex/SegmentPrimitive.lean)
compiles unchanged after deleting all **18 direct `Mathlib.Tactic.*` imports**, retaining
only `HasPrimitives` and `RemovableSingularity`. The removed modules include arithmetic,
ordinal and inclusion tactics unrelated to the subject. This checks those direct imports
against the current pin; it does not claim that tactic facilities disappear from the
transitive import closure. Similar broad blocks occur in foundational files, including
`Painleve/Basic/Equations.lean`, and deserve their own checks.

## Recommended order of work

1. Repair the confirmed false formulations, keeping the pending Leibniz/Haar questions
   separate and recording assumptions and branch choices explicitly.
2. Generalize the primary interfaces with verified redundant hypotheses, then migrate
   callers away from restricted compatibility wrappers. Apply the three independently
   proved hypothesis simplifications.
3. Consolidate core integrals, Wronskians, raising operators and periodic functions, and
   replace substantial repeated proofs with the accessible upstream results.
4. Refactor the hypergeometric logarithmic formulas and the repeated Jacobi/Mathieu
   families. Split the near-limit files along the resulting mathematical boundaries.
5. Rename predicates and public helper APIs coherently; improve semantic docstrings and
   module scope summaries; finish import and linter cleanup.

Validation for this review: the ordinary full build completed successfully (14,914 jobs);
the import survey and all 1,201 source-file length checks pass; the compiled audit and
all 341 narrowed-proof kernel checks pass; the three named hypothesis-simplification
experiments compile with standard axioms only; and the reduced-import file compiles
with strict implicit-variable settings. The inventory preserves the audit sources and
results so the verified findings can be reproduced before implementation.
