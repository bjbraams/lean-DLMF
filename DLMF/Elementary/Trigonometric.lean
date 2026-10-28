/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import DLMF.Elementary.Trigonometric.DirectIdentities
public import DLMF.Elementary.Trigonometric.InverseBranches
public import DLMF.Elementary.Trigonometric.InverseIdentities
public import DLMF.Elementary.Trigonometric.ValuesAndIntegrals

/-!
# Trigonometric and inverse trigonometric functions (DLMF §§4.14–4.27)

Acquisition checked against NIST DLMF on 2026-10-24. Upstream results are recorded in
`MathlibCoverage`, without duplicate wrappers. This module supplies genuinely missing definitions
and statements. Admissions remain explicit. Complex inverse functions use principal logarithms
and square roots off their cuts; their two boundary values are represented separately. General
inverse values are sets, so identities between multivalued functions retain every branch.
Reciprocal functions are totalized at poles; all identities that need finite values state this.

Mathlib's full complex sine/cosine fibers and antiperiodicity provide the inverse families;
integer parity combines the two sine fibers without discarding any branch or endpoint.

The sine orthogonality API is imported from pinned TauCeti. The Bernoulli/Euler and partial-fraction
APIs are existing Mathlib-only `DLMFMathlib` developments. The general-solution and Gudermannian
statements record the necessary singular-solution and sign corrections to the displayed source.
-/
