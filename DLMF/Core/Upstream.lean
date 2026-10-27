/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Tactic.CrossRefAttribute

/-!
# Checked pointers from DLMF items to upstream declarations

Mathlib's `@[dlmf REF]` attribute can only be attached where a declaration is made. For a
DLMF item already formalized upstream (in Mathlib or TauCeti) without such a tag, the command

  dlmf_upstream 8.17.E3 Complex.betaIntegral_eq_Gamma_mul_div "special case: 0 < re a, re b"

records a pointer instead of a duplicate local theorem. The DLMF reference is parsed by the
same parser as `@[dlmf]`, and the declaration must exist, so a renamed upstream declaration
breaks the build rather than leaving a dead pointer. The optional string states how the
upstream statement relates to the DLMF one (see `DLMFIndex.md`: exact, stronger, special case,
different convention, partial), followed by free text.

The pointers are kept in the environment extension `upstreamExt` and harvested, together with
the `@[dlmf]` tags, by `scripts/DumpDLMF.lean`.
-/

public meta section

open Lean Elab Command Mathlib.CrossRef

namespace DLMF

/-- A pointer from a DLMF item to a declaration made elsewhere. -/
structure UpstreamPointer where
  /-- The DLMF reference, as parsed by `@[dlmf]`. -/
  dlmf : String
  /-- The declaration formalizing the item. -/
  declName : Name
  /-- How the declaration relates to the DLMF statement, and free text. -/
  comment : String
  deriving Inhabited

/-- The environment extension storing all `dlmf_upstream` pointers. -/
initialize upstreamExt :
    SimplePersistentEnvExtension UpstreamPointer (Array (Array UpstreamPointer)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun ps => ps
    addEntryFn := fun ps _ => ps
  }

/-- All pointers in the environment, imported and local. -/
def upstreamPointers (env : Environment) : Array UpstreamPointer :=
  let st := PersistentEnvExtension.getState upstreamExt env
  st.2.flatten.appendList st.1

/-- `dlmf_upstream REF decl "relation: comment"` records that the DLMF item `REF` is
formalized by the existing declaration `decl`. -/
syntax (name := dlmfUpstream) "dlmf_upstream " dlmfIdParser ppSpace ident (ppSpace str)? :
  command

elab_rules : command
  | `(dlmf_upstream $id $decl $[$comment]?) => do
    let idStr ← liftCoreM id.getDlmfId
    let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo decl
    modifyEnv (upstreamExt.addEntry · {
      dlmf := idStr, declName := n, comment := (comment.map (·.getString)).getD "" })

end DLMF
