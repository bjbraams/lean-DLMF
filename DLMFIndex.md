# A concordance between DLMF and formal libraries

This note proposes how to organize a community index from the NIST
[Digital Library of Mathematical Functions](https://dlmf.nist.gov/) (DLMF) to formalizations
of its content: Mathlib, TauCeti, open pull requests to either, registries of formalization
work, and projects such as this one. It ends with the pilot implemented in this repository.

## Aim

A reader who looks at a DLMF equation should be able to find out whether it has been
formalized, where, in which form (exact, stronger, restricted, or in a different convention),
and whether the proof is complete. A contributor should be able to see what is missing, chapter
by chapter. The index holds identifiers and links, not formulas, so it stays much smaller than
DLMF and does not reproduce NIST content.

## Prior art

- Mathlib's cross-reference attributes in `Mathlib/Tactic/CrossRefAttribute.lean`:
  `@[stacks]`, `@[kerodon]`, `@[lmfdb]`, `@[oeis]`, `@[wikidata]`, `@[pibase]` and `@[dlmf]`.
  Each records the reference in an environment extension and appends a link to the docstring.
  The `@[dlmf]` attribute parses DLMF's own permalink grammar and takes an optional comment.
- The Stacks project tags, which Mathlib already uses this way, show that a stable external
  key plus an attribute in the source is enough to build a concordance mechanically.
- DLMF's per-chapter Software sections and its Software Index, which play the same role for
  numerical software. A formalization index is a natural sibling.

## Key and granularity

The key is the DLMF permalink identifier, exactly as `@[dlmf]` parses it:

- equations `10.2.E2`, including sub-labels such as `13.6.E11_1`;
- tables `18.3.T1` and, where useful, figures;
- subsections `10.21.ii`, for statements made in prose without an equation number.

Store at this finest level and never finer, so that every key is stable and citable. Prose
results inside one subsection are told apart by the attribute's comment string.

Display at the level of DLMF sections and subsections: one line per unit with coverage counts,
expanding to its equations. Sections are too coarse for a status because one section often mixes
trivial specializations with deep theorems. Equations are too fine for browsing.

One DLMF equation can be covered by several declarations, possibly in several projects, and one
theorem often covers several equations. The index is therefore a many-to-many relation.

## Generate, do not curate

Every fact that changes with the code is harvested from the code:

- which declaration carries which DLMF key;
- where it lives: project, module, file, line, commit, and documentation link;
- whether it is proved, decided by the compiled axiom audit (`Lean.collectAxioms`), not by
  reading the source.

Each project runs a harvester at a pinned commit and publishes a JSON dump. An aggregator joins
the dumps on the DLMF key. Only judgments that the code cannot express are entered by hand.
Experience in this repository supports this: hand-maintained ledgers here had more than 800
out-of-date status labels within two days of active work, while the generated ones are exact by
construction.

## Record

One record per pair of DLMF key and declaration:

- DLMF key, with the DLMF version against which the statement was checked;
- project, full declaration name, kind (theorem, definition), commit or release;
- source link at that commit, and a documentation link where one exists;
- status, from the axiom audit: proved; proved from admissions (no `sorry` of its own, but it
  depends on an admitted lemma); admitted; nonstandard axioms (for example `native_decide`);
- relation to the DLMF statement (see below), and a free-text qualification.

### Relation vocabulary

Special functions need this more than most areas, because totalized functions, branches and
normalizations differ between sources and libraries. A small controlled vocabulary:

- exact;
- stronger (for example valid at the poles of Γ, or for all parameters);
- special case (real arguments only, integer parameters, a smaller sector);
- different convention (normalization, branch, or a totalized value at singular points, such
  as Mathlib's digamma being zero at the poles of Γ);
- partial (one part of a multi-part equation);
- source erratum (the formal development shows the printed statement is false; the record
  links the counterexample).

The relation can be carried in the attribute comment, for example
`@[dlmf 13.11.E3 "stronger"]`, with free text after the keyword.

## Pointers to untagged upstream declarations

Most DLMF content already in Mathlib carries no `@[dlmf]` tag, and an attribute cannot be added
to a declaration from another library. Until upstream declarations are tagged, a downstream
project can record a checked pointer instead. In this repository the command

    dlmf_upstream 8.17.E3 Complex.betaIntegral_eq_Gamma_mul_div "special case: 0 < re a, 0 < re b"

(`DLMF/Core/Upstream.lean`) parses the DLMF key with the `@[dlmf]` parser, requires the
declaration to exist, so that an upstream rename breaks the build instead of leaving a dead
link, and stores the pointer in an environment extension. The harvester reports these records
under the upstream project, with their location and status taken from the upstream declaration,
and marks them as pointers together with the module that recorded them. The string starts with
the relation keyword. Tagging upstream remains the better long-term route; each pointer is also
a candidate tag for a small Mathlib or TauCeti pull request.

## Display order

Within a DLMF key, entries are ordered by source: Mathlib, TauCeti, open pull requests to
Mathlib, open pull requests to TauCeti, other projects found on GitHub, and this project last.
Pull requests to TauCeti rarely name equations; they are attached at chapter or section level
by topic and labelled as related rather than as matches. Entries from pull requests and other
repositories are read from source, not compiled, and are marked unverified.

## Layers outside released code

- Open pull requests to Mathlib and TauCeti: harvest the `@[dlmf …]` lines added in open PR
  diffs through the GitHub API, and regenerate the layer nightly. No convention beyond tagging
  is needed. This layer is transient and is marked as such.
- Registries of formalization work, such as the Palomar registry: if a registry records
  declaration names or DLMF keys, it is one more feed joined on the same key; otherwise it is
  linked at section level. The data model of each registry still has to be examined.

## Coverage and exclusions

To show what is missing, the index needs the full list of DLMF keys per section as the
denominator. It can be derived from the structure of the DLMF site, ideally with NIST's
cooperation. Exclusions must be explicit so that they do not read as gaps: graphics,
applications, software sections, and purely numerical content (tabulated values and decimal
approximations of zeros or constants), each recorded as "excluded" with a reason.

## Size and presentation

The summary view has about one line per DLMF section or subsection. Detail records exist only
for covered keys. Pages show coverage bars per chapter and section, filters by project and
status, search by key or declaration name, and per-equation links to DLMF and to the source.

## Hosting

A small separate repository, outside Mathlib, holding the per-project harvesters, the
aggregator and a generated static site. The proposal can be discussed on the Lean Zulip, since
the `@[dlmf]` attribute exists but nothing yet aggregates it across projects, and later offered
to the DLMF editors as a companion to the Software Index.

## Pilot in this repository

- `scripts/DumpDLMF.lean` is the harvester. Run from the project root after a build:
  `DLMF_DUMP_OUT=dlmf-tags.json lake env lean scripts/DumpDLMF.lean`. It reads the `@[dlmf]`
  environment extension of all of Mathlib, the project and the TauCeti modules the project
  imports, and writes the record above without the relation field. The header records the
  Mathlib and TauCeti revisions from `lake-manifest.json` and this repository's commit. It also
  writes the `dlmf_upstream` pointers, with `"source": "pointer"` and the recording module.
- `scripts/dlmf_ledgers.py` regenerates the declaration links, statuses and module counts of
  the acquisition ledgers (`AiryAcquisition.md`, `DLMF678Acquisition.md`,
  `DLMF111214Acquisition.md`, `DLMF4Acquisition.md`, `DLMF16Acquisition.md`,
  `DLMF17Acquisition.md` and `DLMF19Acquisition.md`–`DLMF23Acquisition.md`) from the dump.
- `scripts/dlmf_index_page.py` renders the dump as a browsable pilot index page (template
  `scripts/dlmf_index_template.html`): `python3 scripts/dlmf_index_page.py dlmf-tags.json
  dlmf-index.html`. It uses the acquisition ledgers and coverage files for the per-section
  denominators where the project has enumerated a DLMF chapter.

On 2026-10-21 (commit `464181a`) the dump has 2,882 records for 2,329 DLMF keys: 19 from
Mathlib, 2,863 from this project, none from the pinned TauCeti. Of the records, 2,376 are proved
and 506 are admitted.
After the `dlmf_upstream` conversion the same day the dump has 3,060 records for 2,424 keys,
including 178 checked pointers (172 to Mathlib, 6 to TauCeti), each verified against the live
DLMF page and the upstream statement: 56 exact, 84 partial, 27 special case, 9 different
convention, 2 stronger.

The 2026-10-24 compiled snapshot has 4,166 records for 3,181 keys. Chapters 4, 16
and 17 now have complete numbered-scope ledgers, including explicit exclusions.
Inserted identifiers such as `16.4.E2_5` remain separate denominator entries.

Limitations of the pilot:

- equation keys carry no subsection, so the page groups by section; the subsection structure
  has to come from DLMF itself;
- relation keywords exist only on `dlmf_upstream` pointers so far, not yet in `@[dlmf]` comments;
- the pull-request and GitHub-wide layers are not implemented; they need an authenticated
  GitHub client, which suits a scheduled job in the separate index repository;
- TauCeti modules not imported by this project are not harvested;
- denominators exist only for the chapters this project has enumerated (Chapters 4, 6–9,
  11–14 and 16–18), and they reflect DLMF version 1.2.8.

Next steps: agree on the relation vocabulary, add a TauCeti harvest over the whole library and
a pull-request layer, obtain the DLMF key list per section, and move the aggregator to a
separate repository.
