# Basic elliptic-function material from the reference books

## Scope and selection

DLMF Chapter 20 concerns theta functions. The comparison here also includes the existing
project coverage of Chapters 19, 22 and 23, rather than counting Jacobi and Weierstrass
identities already formalized elsewhere in the project as new material.

The nine elliptic-function books in References were converted to searchable text for this
survey. Their contents and relevant mathematical sections were compared with the local
code and the pinned Mathlib and TauCeti sources. The extracted texts are working files in
`/tmp/DLMF-elliptic-books`; the PDFs remain the source documents. This note records a
selection of basic theory, rather than claiming a theorem-by-theorem acquisition of all
nine books.

The selected additions are:

- The multiplier ring of a lattice, its integer matrices, algebraic integrality, and the
  imaginary quadratic equation of a noninteger multiplier.
- Maps between lattice curves induced by complex scalars, their kernels, surjectivity,
  injectivity criterion, composition, and the square count of division points.
- The three cases for scalar automorphisms: the general case, the square lattice case,
  and the hexagonal lattice case.
- Construction of elliptic functions from balanced sigma products, with exact
  meromorphic orders, and the sufficient half of Abel's divisor theorem.
- Construction from prescribed simple principal parts using finite sums of zeta
  functions with residues summing to zero.

These are basic structural results about elliptic functions and complex tori. They go
beyond the identities of theta functions in Chapter 20. They also provide explicit
constructions useful for subsequent function theory. The general lattice algebra belongs
to DLMFMathlib; the special-function constructions and curve maps belong to
`DLMF.Weierstrass`.

## Sources and overlap

- **Armitage and Eberlein, Elliptic Functions (2006).** Chapters 2–8 give Jacobi
  functions, periods and general elliptic-function theory, theta functions,
  transformations, Weierstrass functions, and elliptic integrals. Chapter 3, especially
  §3.2 on period modules, and Chapter 7 give the structural perspective used here.
  Most named-function formulas already have homes in Elliptic, Theta, JacobiElliptic,
  EllipticIntegrals and Weierstrass. The later geometry, quintic, arithmetic and
  mechanics chapters are applications rather than the selected basic scope.
- **Chandrasekharan, Elliptic Functions (1985).** Chapters I–II treat periods and
  general properties. Chapter III §5 gives generation of functions with prescribed
  zeros and poles. Chapter IV §3, Theorem 4, pp. 54–55, gives their sigma-product
  representation. The new divisor construction implements its converse, allowing
  repeated and cancelling classes. Chapters V–VIII largely overlap the existing
  theta, Jacobi and modular-function areas. Chapters IX–XI are arithmetic applications.
- **Koecher and Krieg, Elliptic Functions and Modular Forms (2025).** Chapter I §2
  contains the four Liouville theorems and Abel's relation. Section 5 relates lattices
  and elliptic curves. Section 6, especially Theorem 6.5 and the representation theorem
  following it, constructs functions from divisors; §7 discusses division values and
  complex multiplication. These motivate the new divisor, curve-map and multiplier
  results. Chapters II–V develop broader modular-form and arithmetic theory, much of
  it already upstream and outside this selection.
- **Lang, Elliptic Functions, second edition (1987).** Chapter 1 §§1–3 overlaps
  existing general function theory, Weierstrass functions and addition formulas.
  Chapter 1 §4 and Chapter 2 §§1–2 supply lattice maps, division points and isogenies.
  Chapter 1 §5, pp. 19–21, supplies the elementary multiplier and automorphism theory
  implemented here. Chapter 18 §1 gives sigma and zeta functions. The subsequent
  class-field, reduction, complex multiplication reciprocity, and arithmetic theory
  is substantially beyond basic analytic elliptic-function theory.
- **Lawden, Elliptic Functions and Applications (1989).** Chapters 1–6 largely overlap
  existing theta, Jacobi, elliptic-integral and Weierstrass modules. Chapter 8 §§8.1–8.2
  treats general periods and elliptic functions, §8.9 gives sigma representation,
  §8.10 rational representation in Weierstrass functions, and §8.11, pp. 230–232,
  gives expansion in zeta functions and their derivatives. The new residue construction
  realizes the simple-pole part of §8.11. Physical applications and higher modular
  transformations are not included as new basic results.
- **Roy, Elliptic and Modular Functions from Gauss to Dedekind to Hecke (2017).**
  Chapters 2–5 explain AGM, Jacobi transformations and products, Eisenstein's elliptic
  functions, and theta transformations. Chapter 6 §6.4 develops complex analysis in
  elliptic-function theory. These largely overlap existing function identities and
  general theory. The historical Eisenstein summation convention must be distinguished
  from unordered Lean `tsum`; no conditionally convergent ordered series is silently
  identified with an unordered lattice sum here. Later modular-form and arithmetic
  developments are outside the selected scope.
- **Schwalm, Lectures on Selected Topics in Mathematical Physics: Elliptic Functions
  and Elliptic Integrals (2015).** Chapters 1–2 cover Jacobi differential equations
  and oscillators; Chapters 3–4 reduce quartics and general elliptic integrals.
  The existing JacobiODE, Elliptic.JacobiIdentities, Elliptic.PendulumEnergy and
  Elliptic.BookReductions modules already provide related content. The newly selected
  gaps are general complex function theory rather than another pendulum or reduction
  definition. Sine-Gordon and the other physical applications are outside this selection.
- **Takebe, Elliptic Integrals and Elliptic Functions (2023).** Chapters 10–12 cover
  Abel–Jacobi, general elliptic functions, and Weierstrass functions. Chapters 15–17
  largely overlap existing theta and Jacobi material. The new divisor existence
  theorem is a genus-one Abel construction; it does not assert the full identification
  of an Abelian integral with uniformization from Chapter 10. The general algebraic
  addition theorem of Chapter 13 and its characterization in Chapter 14 remain further
  basic development candidates.
- **Weil, Elliptic Functions According to Eisenstein and Kronecker (1976).**
  Chapters III–IV develop lattice pole sums, their relations, and products; Chapters
  V–VI give variations, and Chapters VII–IX develop Kronecker's double series and
  arithmetic applications. The absolutely convergent Weierstrass and zeta lattice
  constructions overlap the existing code. Eisenstein's order-dependent sums for
  exponents one and two, and Kronecker's double series, require their own convergence
  conventions; they are not represented by new copies of existing Weierstrass functions.

## Implementation and theorem inventory

All six new modules contain completed proofs and introduce no admissions.

- `DLMFMathlib.Analysis.Complex.LatticeMultipliers` uses TauCeti's
  `AddSubgroup.multiplierRing` directly on `L.lattice.toAddSubgroup`.
  It proves the two-generator criterion, existence of an integer action
  matrix, a monic integer quadratic equation, algebraic integrality, the real-multiplier
  criterion, and negative discriminant for every noninteger multiplier. It uses Mathlib's
  namespaces and lattice API, as required for the general supporting layer.
- `DLMF.Weierstrass.LatticeHomomorphisms` defines `latticeCurveHom`. Its point formula
  sends the point of `z` to the point of `αz`; its kernel criterion is `αz ∈ Μ`.
  Nonzero scalar maps are surjective. Injectivity means there are no extra points over
  the target lattice. Composition multiplies scalars; natural-number scalars induce
  multiplication on the curve. `natCard_torsionBy_latticeCurve` proves the count `N²`
  for `N ≠ 0`. This module establishes these group-theoretic results, without claiming
  a classification of all analytic homomorphisms or a general isogeny degree formula.
- `DLMF.Weierstrass.ComplexMultiplication` proves the exact invariant-weight criterion
  for scalar lattice automorphisms. It derives the general `±1` case, the fourth-root
  case `g₃ = 0`, and the sixth-root case `g₂ = 0`, together with the universal
  twelfth-root and absolute-value-one consequences.
- `DLMF.Weierstrass.Basic.ZetaProperties` bridges the existing DLMF and TauCeti zeta
  series by uniqueness of their sums and exports meromorphy. It preserves both
  definitions, including their assigned regular parts at lattice poles. The redundant
  private meromorphy proof in Weierstrass.Series is replaced by this public theorem.
- `DLMF.Weierstrass.PrescribedResidues` defines `zetaSum`, computes its quasi-period,
  proves periodicity when the residues sum to zero, and proves global meromorphy.
  It computes the derivative off the pole classes and proves analyticity after
  subtraction of each prescribed simple principal part, under separation of that class
  from the other specified classes. No nonzero-residue assumption is imposed.
- `DLMF.Weierstrass.PrescribedDivisors` defines `sigmaProduct` and `sigmaQuotient`.
  It proves the product multiplier formula, periodicity under exact balance of
  representatives, analytic/meromorphic properties, and the zero criterion on the
  regular denominator locus. The meromorphic-order formula handles repeated locations
  and cancellation. `exists_elliptic_with_prescribed_orders` handles the full balance
  condition modulo the lattice by shifting one pole representative. The empty divisor
  gives the constant one. This is the sufficient direction of Abel's theorem.

## Upstream reuse and conventions

No local copy of complex uniformization, the lattice classification theorem, or explicit
torsion coordinates is introduced. The curve-map and automorphism proofs use:

- `AddSubgroup.multiplierRing` and `AddSubgroup.mem_multiplierRing` from pinned
  TauCeti for the general multiplier-ring definition and membership criterion.
- `PeriodPair.weierstrassPointEquiv`, `weierstrassPoint_surjective`,
  `weierstrassPoint_eq_zero_iff`, and `weierstrassPoint_nsmul` from pinned TauCeti.
- `PeriodPair.torsionEquivCoordinates` from pinned TauCeti for the square count.
- `PeriodPair.lattice_eq_iff_g₂_eq_and_g₃_eq`, `g₂_smul`, `g₃_smul`, and
  `weierstrassCurve_Δ_ne_zero` from pinned TauCeti for automorphisms.
- `PeriodPair.quasiPeriod` and `weierstrassZeta_add_coe` from pinned TauCeti through
  the proved bridge to the project's canonical zeta series.

The upstream curve uses coordinates `(℘, ℘'/2)` and equation
`y² = x³ - (g₂/4)x - g₃/4`. PeriodPair stores full periods, whereas
`DLMF.Weierstrass.HalfPeriods`
stores half-periods. Existing branches and definitions are preserved. The sigma quotient's
assigned value at a zero denominator is not used to decide poles or cancelled divisors;
the order theorem is stated in terms of meromorphic germs.

## Remaining basic gaps

The existing `DLMFMathlib.Analysis.Complex.EllipticDivisors` contains admitted targets for
finite poles in a cell, zero residue sum, absence of elliptic functions of order one,
and equality of value and pole counts. The existing
`DLMF.Weierstrass.exists_polynomial_weierstrass_representation` is also admitted.
They remain so; none supplies a premise for the new proofs.

Further natural basic targets include necessity in Abel's divisor theorem, the complete
partial-fraction representation with higher poles, the dimensions and bases of bounded-pole
spaces, the general algebraic addition theorem, and the analytic classification and degree
of general torus isogenies. The Eisenstein–Kronecker approach also warrants separate
ordered-series definitions. These are identified gaps, not claims of completed coverage.

## Validation

The integration record is `reports/EllipticBooksValidation.json`. It records the final
build and direct checks, theorem axiom audits, source hashes, source-PDF metadata, and
the import-graph comparison. The new modules are registered in their area or support
umbrellas; the zeta properties are also registered in Weierstrass.Basic.

The full ordinary build passes (19,778 jobs), as does the targeted build of the ten
affected source and entry modules (14,169 jobs). All ten direct Lean checks pass; the
six new modules also pass with warnings treated as errors. All 45 new declarations
have only standard axioms, with no `sorryAx`. File/line-length and whitespace checks
pass. There are no new two-way area pairs, foundational violations, forbidden Basic
closure dependencies, missing imports or file cycles.
