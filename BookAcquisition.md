# Acquisition from the six reference-book synopses

This acquisition compares every synopsis entry with the pinned Mathlib, TauCeti and
current DLMF project. It adds meaningful definitions and missing mathematical statements
with book, chapter/section and statement provenance. Most new theorem targets are admitted;
coverage of a statement does not imply a completed proof.

All **927 synopsis entry groups** now have coverage mappings: Temme 168, Olver 227,
Duverney 197, Rao–Lakshminarayanan 125, AAR 85 and Kristensson 125. Valid missing
content has been acquired; proposed revisions of defective or insufficiently specified
statements are retained for review. The acquisition preserved the six SYNOPSIS files; the subsequent approved
correction round updates the four affected synopses and their errata records.

The acquisition adds **481 Lean modules**, with **1,581 explicit admitted targets**.
It also adds proved definitions, basic interfaces and mathematical results. At acquisition
handoff the project contained 2,401 literal `sorry` occurrences: the original 820 and
the new 1,581. The approved correction round proves the two principal-strip bridges,
reducing the current total to **2,399**. Acquisition coverage must not be confused with completed proofs.

- [Temme audit](BookAcquisition-Temme.md), with dedicated reviews of
  [Chapter 1](BookAcquisition-Temme-Chapter1.md),
  [Chapter 2](BookAcquisition-Temme-Chapter2.md),
  [Chapter 6](BookAcquisition-Temme-Chapter6.md),
  [Chapters 7–8](BookAcquisition-Temme-Chapters7-8.md),
  [Chapter 11](BookAcquisition-Temme-Chapter11.md), and
  [Chapter 12](BookAcquisition-Temme-Chapter12.md).
- [Olver audit](BookAcquisition-Olver.md), with dedicated reviews of
  [Chapters 1–4](BookAcquisition-Olver-Chapters1-4.md),
  [Chapters 5–7](BookAcquisition-Olver-Chapters5-7.md), and the
  [Chapter 13 network](BookAcquisition-Olver-Chapter13-Network.md).
- [Duverney audit](BookAcquisition-Duverney.md).
- [Rao–Lakshminarayanan audit](BookAcquisition-LaoLaksh.md), with
  [Chapter 1](BookAcquisition-LaoLaksh-Chapter1.md) and
  [Chapter 3](BookAcquisition-LaoLaksh-Chapter3.md).
- [Andrews–Askey–Roy audit](BookAcquisition-AAR.md).
- [Kristensson audit](BookAcquisition-Kristensson.md).

The main mathematical additions cover continued and logarithmic branches of special
functions, ordinary versus absolute convergence, finite sums with only their actual
nonvanishing denominator conditions, contour integrals, uniform asymptotic expansions,
polynomial and representation-theoretic identities, and quantitative ODE error bounds.
General mathematics belongs to DLMFMathlib; special-function material belongs to DLMF.
Every new module is registered in its library or area entry point.

New proofs include finite spin matrices and Pauli identities, maximal-real-part indicial
root selection, Stirling positivity, arithmetic–geometric mean gap identities, ordinary
alternating digamma sums, the normalized Bessel limit at zero, polynomial Legendre
addition, six Airy sign and monotonicity results, Lipschitz error transfer, exponential
majorants, circuit basis change and the recessive circuit multiplier. Transitive axiom
audits distinguish these proofs from targets depending on `sorryAx`.

At acquisition handoff the full ordinary build passed (**19,494 jobs**) and all
**550 changed sources and entry modules** passed strict Lean checks with both
implicit-variable options disabled. The acquisition integration record preserves
that snapshot; subsequent approved correction validation is recorded separately. Import, line/file-length and whitespace checks pass.
Every new module is reachable; there are no foundational import violations, forbidden
Basic import-closure dependencies, missing project imports or file-import cycles.
The [acquisition integration record](reports/BookAcquisition20261114.json) preserves
that snapshot’s source hashes, counts and import comparison. The approved repairs,
raw-connection API renames and bridge proofs have a separate
[correction record](reports/BookCorrections20261114.json).

The import graph has 11 new two-way area pairs, with no file cycles:

- Airy / AsymptoticApproximations; Airy / Bessel.
- AlgebraicAnalytic / Legendre; AlgebraicAnalytic / OrthogonalPolynomials.
- AsymptoticApproximations / Confluent; Bessel / Hypergeometric.
- Constants / Zeta; Gamma / Selberg.
- GeneralizedHypergeometric / Hypergeometric; IncompleteGamma / Statistical.
- QHypergeometric / QSeries.

The q-Gegenbauer value-at-zero lemma moved unchanged into its foundational home.
The generic slit-plane estimate was renamed to avoid a pinned TauCeti declaration;
its upstream reuse and public rename are recorded in CREDITS and the rename map.
Preexisting unrelated work is retained.

[Revision notes](BookAcquisition-RevisionNotes.md) retain **21 mathematical review topics**:
suspected false statements, necessary qualifications and proposed synopsis repairs.
Two printed Olver qualifications with explicit counterexamples are also recorded in
[ERRATA-Olver.md](ERRATA-Olver.md). The agreed corrections are now applied; remaining interpretation and proof
questions are explicitly distinguished from settled repairs. The acquisition’s source evidence is retained alongside the applied dispositions.
Existing theorem hypotheses and conclusions are preserved through the recorded
connection-helper renames; deprecated aliases retain the old public spellings.
The raw formula bodies and canonical continued-function definitions are preserved. Dependency pins, build settings and the shared Lake symlink are unchanged.
