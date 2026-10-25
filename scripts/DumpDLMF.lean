/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
import Mathlib
import DLMFMathlib
import DLMF
import DLMF.Core.Upstream

/-!
# Dump of all `@[dlmf]` cross-references

Writes every declaration carrying Mathlib's `@[dlmf REF "comment"]` attribute
(`Mathlib/Tactic/CrossRefAttribute.lean`) in the imported environment to a JSON file, one
entry per (DLMF reference, declaration) pair, with its project, module, source location and
proof status. It also writes the checked pointers recorded with `dlmf_upstream`
(`DLMF/Core/Upstream.lean`) from DLMF items to untagged declarations of Mathlib or TauCeti:
these entries have `"source": "pointer"` and name the module that recorded them in
`recordedIn`; tagged entries have `"source": "tag"`. A pointer that duplicates a tag of the
same declaration is omitted. The status comes from the axiom audit (`Lean.collectAxioms`), not from the
source text: `proved` means only `propext`, `Classical.choice` and `Quot.sound` are used,
`admitted` means `sorryAx` occurs in the transitive dependencies, and `nonstandard` means some
other axiom (for example `Lean.ofReduceBool` from `native_decide`) occurs. For admitted
theorems, `sorryDirect` records whether `sorryAx` occurs in the declaration's own proof
(`false`: it only depends on other admissions; absent: the proof term was not available).

The environment is that of the imports above: all of Mathlib, and the project libraries
together with the TauCeti modules they import. Run it from the project root, after a
successful `lake build`, as

  DLMF_DUMP_OUT=dlmf-tags.json lake env lean scripts/DumpDLMF.lean

The output path defaults to `dlmf-tags.json` in the current directory.
-/

open Lean Mathlib.CrossRef

namespace DumpDLMF

/-- The standard axioms of Lean and Mathlib. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Project of a module, with the source root of its files relative to the Lake root. -/
def projectOf (mod : Name) : String × String :=
  match mod.getRoot.toString with
  | "Mathlib" => ("Mathlib", ".lake/packages/mathlib/")
  | "TauCeti" => ("TauCeti", ".lake/packages/TauCeti/")
  | "DLMF" => ("lean-DLMF", "")
  | "DLMFMathlib" => ("lean-DLMF", "")
  | "ToMathlib" => ("lean-codes", "../lean-codes/")
  | "Carlson" => ("lean-codes", "../lean-codes/")
  | r => (r, "")

/-- Source path of a module relative to its package root. -/
def modulePath (mod : Name) : String :=
  "/".intercalate (mod.components.map Name.toString) ++ ".lean"

/-- Revision and repository URL of each project, from `lake-manifest.json` and `git`. -/
def projectInfo : IO Json := do
  let manifest ← IO.FS.readFile "lake-manifest.json"
  let some pkgs := (Json.parse manifest).toOption.bind (·.getObjValD "packages" |>.getArr?.toOption)
    | throw <| IO.userError "cannot read lake-manifest.json"
  let pick (name : String) : Json := Id.run do
    for p in pkgs do
      if p.getObjValD "name" == Json.str name then
        return Json.mkObj [("url", p.getObjValD "url"), ("rev", p.getObjValD "rev")]
    return Json.null
  let git (args : Array String) : IO String := do
    let out ← IO.Process.output { cmd := "git", args }
    return out.stdout.trimAscii.toString
  let rev ← git #["rev-parse", "HEAD"]
  let dirty := !(← git #["status", "--porcelain", "--untracked-files=no"]).isEmpty
  let url ← git #["remote", "get-url", "origin"]
  return Json.mkObj [("Mathlib", pick "mathlib"), ("TauCeti", pick "TauCeti"),
    ("lean-DLMF", Json.mkObj [("url", url), ("rev", rev), ("dirty", dirty)])]

/-- Strip a trailing `.git` from a repository URL. -/
def repoBase (url : String) : String :=
  if url.endsWith ".git" then (url.dropEnd 4).toString else url

/-- One JSON entry for a DLMF cross-reference `tag` of the declaration `n`. -/
def entry (info : Json) (n : Name) (tag comment source : String) (recordedIn : Option Name) :
    CoreM Json := do
  let env ← getEnv
  let mod : Name := match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => .anonymous
  let (project, root) := projectOf mod
  let file := root ++ modulePath mod
  let ranges ← findDeclarationRanges? n
  let line := ranges.map (·.range.pos.line)
  let endLine := ranges.map (·.range.endPos.line)
  let ci := (env.setExporting false).find? n
  let kind := match ci with
    | some (.thmInfo _) => "theorem"
    | some (.defnInfo _) => "def"
    | some (.opaqueInfo _) => "opaque"
    | some (.inductInfo _) => "inductive"
    | some (.ctorInfo _) => "constructor"
    | some (.axiomInfo _) => "axiom"
    | _ => "other"
  let axs ← collectAxioms n
  let extra := axs.filter (!standardAxioms.contains ·)
  let status :=
    if extra.contains ``sorryAx then "admitted"
    else if extra.isEmpty then "proved" else "nonstandard"
  let direct : Option Bool := match ci with
    | some (.thmInfo v) | some (.defnInfo v) =>
      if status == "admitted" then some (v.value.getUsedConstants.contains ``sorryAx) else none
    | _ => none
  let proj := info.getObjValD project
  let srcUrl := match proj.getObjValD "url", proj.getObjValD "rev", line with
    | .str u, .str r, some l => Json.str s!"{repoBase u}/blob/{r}/{modulePath mod}#L{l}"
    | _, _, _ => Json.null
  let docUrl := if project == "Mathlib" then
      Json.str s!"https://leanprover-community.github.io/mathlib4_docs/{(modulePath mod).dropEnd 5}.html#{n}"
    else Json.null
  return Json.mkObj <| [
    ("dlmf", Json.str tag),
    ("dlmfUrl", Json.str (Database.dlmf.url tag)),
    ("comment", Json.str comment),
    ("source", Json.str source),
    ("recordedIn", match recordedIn with | some m => Json.str m.toString | none => Json.null),
    ("decl", Json.str n.toString),
    ("kind", Json.str kind),
    ("project", Json.str project),
    ("module", Json.str mod.toString),
    ("file", Json.str file),
    ("line", toJson line),
    ("endLine", toJson endLine),
    ("sourceUrl", srcUrl),
    ("docUrl", docUrl),
    ("status", Json.str status),
    ("axioms", toJson (extra.map Name.toString))] ++
    (match direct with | some b => [("sorryDirect", Json.bool b)] | none => [])

/-- All DLMF tags in the environment, sorted by declaration name and tag. -/
def dlmfTags (env : Environment) : Array Tag :=
  let st := PersistentEnvExtension.getState tagExt env
  (st.2.flatten.appendList st.1).filter (·.database == .dlmf)
    |>.qsort fun a b => a.declName.toString < b.declName.toString ||
      (a.declName == b.declName && a.tag < b.tag)

/-- All `dlmf_upstream` pointers with the module that recorded them. -/
def upstreamPointers (env : Environment) : Array (DLMF.UpstreamPointer × Name) :=
  let st := PersistentEnvExtension.getState DLMF.upstreamExt env
  let imported := st.2.mapIdx fun i ps =>
    ps.map fun p => (p, env.header.moduleNames[i]!)
  imported.flatten ++ (st.1.toArray.map fun p => (p, env.mainModule))

end DumpDLMF

open DumpDLMF in
#eval show CoreM Unit from do
  let out := (← IO.getEnv "DLMF_DUMP_OUT").getD "dlmf-tags.json"
  let info ← projectInfo
  let tags := dlmfTags (← getEnv)
  let mut entries ← tags.mapM fun t => entry info t.declName t.tag t.comment "tag" none
  for (p, m) in upstreamPointers (← getEnv) do
    unless tags.any (fun t => t.declName == p.declName && t.tag == p.dlmf) do
      entries := entries.push (← entry info p.declName p.dlmf p.comment "pointer" (some m))
  let count (p : Json → Bool) := (entries.filter p).size
  let summary := Json.mkObj [("entries", toJson entries.size),
    ("pointers", toJson (count (·.getObjValD "source" == "pointer"))),
    ("proved", toJson (count (·.getObjValD "status" == "proved"))),
    ("admitted", toJson (count (·.getObjValD "status" == "admitted"))),
    ("nonstandard", toJson (count (·.getObjValD "status" == "nonstandard")))]
  let doc := Json.mkObj [("format", "dlmf-tags/1"), ("projects", info),
    ("summary", summary), ("entries", Json.arr entries)]
  IO.FS.writeFile out (doc.pretty ++ "\n")
  IO.println s!"{out}: {summary.compress}"
