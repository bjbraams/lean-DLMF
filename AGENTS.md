# Project instructions — lean-DLMF

Before working, read and follow [the shared Lean instructions](../lean-codes/AGENTS.common.md),
then apply the project-specific rules below. Resolve that path relative to this file.
Local rules take precedence over the shared defaults. If the shared file is unavailable,
report that fact rather than proceeding without it.

## Build settings

- Lake root: the directory containing this `AGENTS.md`.
- Build output: `.lake/build-DLMF`; preserve the matching `buildDir` in `lakefile.toml`.
- Ordinary build command: `lake build > /tmp/DLMF-build.log 2>&1`.

## Project

This project formalizes special functions following the NIST Digital Library of Mathematical
Functions (DLMF). It began as a formalization of Special Functions by Andrews, Askey and Roy
(henceforth AAR) and was renamed from lean-AAR to lean-DLMF on 2026-10-21, when the DLMF
chapters became the organizing principle. AAR, Temme, Beals–Wong and Duverney remain
supporting sources. The PDF sources are in the References subdirectory. The Lean code lives
under `DLMF/`, one directory per area; the older areas still follow the arrangement of AAR.
Our concern is with results in DLMF and AAR that are not yet in Mathlib. We do not insist
on a faithful sequential reproduction of either source. Instead, we use them to identify
gaps in the special functions coverage of Mathlib and then we attempt to fill in those gaps.

DLMF has the focus of our attention. Results that come only from AAR or the other
supporting sources and have no DLMF counterpart (for example Apéry's theorem, the
Hasse–Davenport relation, the finite-field Selberg integral, Siegel's inequality,
Vietoris's inequality and Favard's theorem) are retained, admissions included, but have lower priority: plan proof
rounds and new development around DLMF statements first. The Askey–Gasper inequality
has a DLMF counterpart in 16.23.E1, and the Ramanujan partition congruences are stated in
DLMF 27.14(v); both remain in the DLMF priority scope.

## Dependencies and import layers

- `DLMFMathlib/` (modules `DLMFMathlib.*`, renamed from `ToMathlib/` on 2026-10-25) holds
  general results that are not specific to special functions (Euler polynomials,
  Euler–Maclaurin and Boole summation, asymptotic expansions, Watson's lemma), in the
  namespaces of the Mathlib APIs they extend. `DLMFMathlib` may import Mathlib, TauCeti and
  lean-codes, never `DLMF`; `DLMF` modules may import `DLMFMathlib`. This includes the
  existing TauCeti prime-number-theorem imports in the general number-theory support.
- lean-codes is a Lake path dependency (package `LeanCodes`, `../lean-codes`, since
  2026-10-25). Its modules (`Carlson.*`, `Pochhammer.*`, `Dirichlet.*`, its `ToMathlib.*`, …)
  are imported directly; never copy them here and never edit lean-codes from this project.
  The former mirrors `ToMathlib/Analysis/Integral/Laplace.lean` and
  `ToMathlib/Analysis/Complex/Carlson.lean` now come from lean-codes. Building lean-DLMF also
  builds lean-codes modules into lean-codes' own build directory (`.lake/build-codes`).
- The top-level module prefix `ToMathlib` belongs to lean-codes. Lean locates a module's
  build files by its package, so two packages must never share a top-level prefix; put new
  general results of this project under `DLMFMathlib/`.
- Purpose of the foundational layer (2026-11-01). The `Basic` files are the part of the
  library that we offer to the TauCeti and Mathlib communities as the starting point for
  bringing DLMF into TauCeti first and Mathlib later. A reader must be able to work from the
  foundational layer alone: it contains the central definitions of every DLMF chapter in
  scope, together with their basic API, and it depends on nothing outside Mathlib, TauCeti,
  `DLMFMathlib` and the foundational layer itself.
- Foundational layout (adopted 2026-10-30). Use `Basic.lean` for a small foundational
  file or an umbrella; larger collections use descriptive files under `Basic/`. Each
  mathematical definition has exactly one canonical home. Preserve names, namespaces,
  statements, branches, normalizations and definition bodies when reorganizing files.
- Content of the foundational layer (refined 2026-11-01). For each central function or
  family of a chapter, the foundational layer holds:
  - the definition, with a docstring stating its domain, branch and normalization;
  - unfolding, `simp` and special-value lemmas (values at `0`, at integer parameters and at
    exceptional parameters);
  - symmetries, parity and conjugation;
  - continuity, differentiability or analyticity on the stated domain;
  - the defining differential equation, recurrence or functional equation, and the
    Wronskian where DLMF gives one;
  - the bridge to the corresponding Mathlib or TauCeti function where one exists.

  All of these are proved from foundational imports only. Put such properties in files
  below `Basic/` (for example `Airy/Basic/Properties.lean`) so that the definition files
  stay short. A theorem moved down keeps its name, statement, `dlmf` tags and docstring; only
  its proof may change. Where the existing proof sits on a deep theorem-layer stack, give
  the theorem a new proof from foundational imports rather than moving the stack down, and
  do not leave a duplicate in the theorem layer. Only fully proved results go into the
  foundational layer: no `sorry` and no dependence on admitted lemmas. Everything else
  (asymptotics, zeros, integrals, expansions, inequalities, transformations, computation)
  belongs to the theorem layer, as do auxiliary definitions used only there (expansion
  coefficients, error-bound data, reduction data, zero-counting functions).
- A foundational module (`Basic.lean`, any file below `Basic/`, `DLMF.Core.Basic`, or a
  remaining legacy `Defs.lean`/`Definitions.lean`) may import only Mathlib, TauCeti,
  `DLMFMathlib` and other foundational modules. It must not import a DLMF theorem module
  (even in its own area), a non-foundational `DLMF.Core` module, or a lean-codes module.
  The import closure of `DLMF.Basic` must contain no lean-codes module, so a `DLMFMathlib`
  module imported by a foundational file must not import lean-codes either. A definition
  that needs lean-codes (for example `symEllIntR`, built on Carlson's `R`-function) lives in
  the theorem layer. `DLMF.Core.Basic` holds the shared conventions (improper integrals,
  principal values, segment primitives, sector filters, continued fractions); the other
  `DLMF.Core` modules are theorem-layer modules.
- `DLMF.Basic` is the foundational entry point. When adding a new `Basic.lean` entry
  point, include it there. The complete area and top-level umbrellas may import both
  foundational and theorem modules.
- There is no hierarchy between areas: imports in both directions between areas are
  allowed, and only the file graph must be acyclic. A bridge theorem imports the
  foundational modules it connects. If a definition or lemma is needed below its
  current file, move it down unchanged rather than copying it or adding a theorem-file
  dependency to a foundation.
- At integration run `scripts/import_survey.py`. Report new two-way area pairs. The
  survey checks the imports of the entire foundational layer (including `Basic/`
  submodules and same-area imports), the import closure of `DLMF.Basic`, missing project
  modules and file-import cycles. These violations fail regardless of the two-way-area
  baseline.

Mathlib and TauCeti are allowed throughout the DLMF library, including when filling
existing admissions. Preserve complex branches, normalizations, exceptional parameters
and the meaning of totalized series and integrals when adopting upstream statements.

## DLMF statement acquisition

- Cover definitions and mathematical theorems in the selected DLMF scope, including
  results stated in prose. Exclude graphical results and application notes.
- Purely numerical results are out of scope: tabulated function values, decimal values of
  zeros, constants or expansion coefficients (for example γ ≈ 0.5772156649). Exact values
  and asymptotic expansions remain in scope. A crude numerical bound may be proved as an
  untagged helper lemma when a proof needs it (for example `γ < 3/5` in
  `DLMF/Gamma/Inequalities.lean`). Record excluded items in the acquisition ledgers as
  "excluded: numerical".
- When a result is already in Mathlib, record a comment and a precise pointer to
  the upstream declaration instead of reproving it locally. Preserve any domain
  or branch differences when distinguishing upstream coverage from missing results.
