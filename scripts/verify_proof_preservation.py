#!/usr/bin/env python3
"""Compare Lean declaration statements, tags and definitions with a committed baseline.

This is a lexical source audit, complementing Lean builds and #print axioms checks.
It recognizes the project's namespace and declaration layout; the Lean kernel remains
responsible for checking proofs and their dependencies.
"""

import argparse
import bisect
import collections
import hashlib
import json
import re
import subprocess
from pathlib import Path


def strip_comments(text):
    out = list(text)
    i = 0
    depth = 0
    quoted = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i : i + 2] = "  "
                depth += 1
                i += 2
                continue
            if text.startswith("-/", i):
                out[i : i + 2] = "  "
                depth -= 1
                i += 2
                continue
            if text[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if quoted:
            if text[i] == "\\":
                i += 2
                continue
            if text[i] == '"':
                quoted = False
            i += 1
            continue
        if text.startswith("/-", i):
            out[i : i + 2] = "  "
            depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0:
                j = len(text)
            out[i:j] = " " * (j - i)
            i = j
            continue
        if text[i] == '"':
            quoted = True
        i += 1
    return "".join(out)


attrs = r"(?:@\[[^\n]*\][ \t]*)*"
mods = r"(?:(?:private|protected|noncomputable|public|nonrec|partial|unsafe)\s+)*"
pat = re.compile(
    r"^"
    + attrs
    + mods
    + r"(def|abbrev|theorem|lemma|opaque|axiom|structure|inductive|class)\s+([^\s(:{\[]+)",
    re.M,
)
scopes = re.compile(
    r"^" + attrs + mods + r"(namespace\s+(\S+)|section(?:\s+\S+)?|end(?:\s+\S+)?)[ \t]*$", re.M
)
stop = re.compile(
    r"^(?:end(?:\s+\S+)?|section(?:\s+\S+)?|namespace\s+\S+|attribute\s|open\s|set_option\s|@\[|public import\s|import\s)",
    re.M,
)


def dlmf_attribute_groups(text):
    """Yield attribute endpoints and DLMF entries, ignoring other attributes.

    Commas and brackets inside quoted tag comments do not delimit attributes.
    """
    offset = 0
    while True:
        start = text.find("@[", offset)
        if start < 0:
            return
        i = start + 2
        quoted = False
        depth = 1
        entry_start = i
        entries = []
        while i < len(text) and depth:
            c = text[i]
            if quoted:
                if c == "\\":
                    i += 2
                    continue
                if c == '"':
                    quoted = False
            elif c == '"':
                quoted = True
            elif c == "[":
                depth += 1
            elif c == "]":
                depth -= 1
                if depth == 0:
                    entries.append(text[entry_start:i])
            elif c == "," and depth == 1:
                entries.append(text[entry_start:i])
                entry_start = i + 1
            i += 1
        tags = [entry for entry in entries if re.match(r"\s*dlmf(?:\s|$)", entry)]
        if tags:
            yield i, "".join(",".join(tags).split())
        offset = i


def declaration_docstring(text, line):
    """Read the declaration's preceding docstring, allowing intervening attributes."""
    prefix = "\n".join(text.splitlines()[: line - 1]).rstrip()
    prefix = re.sub(r"(?:@\[[^\[\]]*\]\s*)+$", "", prefix).rstrip()
    if not prefix.endswith("-/"):
        return None
    start = prefix.rfind("/--")
    return prefix[start:] if start >= 0 else None


def mathematical_docstring(text):
    """Ignore layout and obsolete admission markers when comparing moved mathematics."""
    return "".join(text.replace("**Admitted.** ", "").split()) if text else None


def parse(text, p):
    text = strip_comments(text)
    decls = list(pat.finditer(text))
    tagsets = collections.defaultdict(list)
    keywords = [x.start(1) for x in decls]
    for endpoint, tags in dlmf_attribute_groups(text):
        k = bisect.bisect_left(keywords, endpoint)
        if k < len(decls):
            tagsets[k].append(tags)
    events = iter(scopes.finditer(text))
    event = next(events, None)
    ns = ""
    stack = []
    out = []
    for i, m in enumerate(decls):
        while event is not None and event.start() < m.start():
            cmd, opened = event.group(1), event.group(2)
            if cmd.startswith("namespace "):
                stack.append(ns)
                ns = (
                    opened.removeprefix("_root_.")
                    if opened.startswith("_root_.")
                    else ".".join(filter(None, [ns, opened]))
                )
            elif cmd.startswith("section"):
                stack.append(ns)
            elif stack:
                ns = stack.pop()
            event = next(events, None)
        command = text[m.start() : decls[i + 1].start() if i + 1 < len(decls) else len(text)]
        head, *b = command.split(":=", 1)
        body = b[0] if b else ""
        body = stop.split(body)[0]
        rawname = m.group(2)
        name = (
            rawname.removeprefix("_root_.")
            if rawname.startswith("_root_.")
            else ".".join(filter(None, [ns, rawname]))
        )
        head = head[head.index(m.group(1)) :]
        out.append(
            dict(
                tags=tagsets[i],
                name=name,
                file=p,
                kind=m.group(1),
                head="".join(head.split()),
                body="".join(body.split()),
                private=bool(re.match(r"(?:@\[[^\n]*\]\s*)*private\s", command)),
                sorry=bool(re.search(r"\bsorry\b", body)),
                line=text.count("\n", 0, m.start()) + 1,
            )
        )
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--new-public-names")
    parser.add_argument(
        "--approved-corrections",
        help="JSON record of user-approved theorem corrections with exact old and new headers",
    )
    args = parser.parse_args()
    paths = subprocess.check_output(
        ["git", "ls-tree", "-r", "--name-only", args.baseline, "DLMF", "DLMFMathlib"], text=True
    ).splitlines()
    paths = [p for p in paths if p.endswith(".lean")]
    objects = subprocess.check_output(
        ["git", "cat-file", "--batch"],
        input="".join(args.baseline + ":" + p + "\n" for p in paths).encode(),
    )
    sources = {}
    offset = 0
    for p in paths:
        end = objects.index(b"\n", offset)
        size = int(objects[offset:end].split()[-1])
        offset = end + 1
        sources[p] = objects[offset : offset + size].decode()
        offset += size + 1
    before = [d for p, s in sources.items() for d in parse(s, p)]
    current = {
        str(p): p.read_text()
        for root in ["DLMF", "DLMFMathlib"]
        for p in Path(root).rglob("*.lean")
    }
    after = [d for p, s in current.items() for d in parse(s, p)]
    old = collections.defaultdict(list)
    new = collections.defaultdict(list)
    for d in before:
        old[d["name"]].append(d)
    for d in after:
        new[d["name"]].append(d)
    issues = collections.defaultdict(list)
    approvals = {}
    if args.approved_corrections:
        record = json.loads(Path(args.approved_corrections).read_text())
        if record.get("status") != "applied with user approval":
            parser.error("the correction record must state that user approval was received")
        approvals = {item["declaration"]: item for item in record["items"]}
    approved_changes = set()

    def approved(d, e):
        item = approvals.get(d["name"], {})
        return (
            d["kind"] in ["theorem", "lemma"]
            and e["kind"] == d["kind"]
            and d["head"] == item.get("baseline_head")
            and e["head"] == item.get("approved_head")
            and d["tags"] == e["tags"]
            and d["private"] == e["private"]
        )

    moves = []
    private_moves = []
    moved_docs_checked = 0
    removed_admission_markers = []

    def shape(d):
        return re.sub(r"^(def|abbrev|opaque)[^({\[:]+", r"\1", d["head"])

    for d in before:
        choices = [e for e in new[d["name"]] if e["private"] == d["private"]]
        same = [e for e in choices if e["head"] == d["head"]]
        if d["private"]:
            if d["kind"] not in ["def", "abbrev", "opaque"]:
                if choices and not d["sorry"] and all(e["sorry"] for e in choices):
                    issues["newAdmissionsInExistingProofs"].append(d["name"])
                continue
            exact = [e for e in same if e["body"] == d["body"]]
            if exact:
                continue
            relocated = [
                e
                for e in after
                if e["kind"] == d["kind"] and e["body"] == d["body"] and shape(e) == shape(d)
            ]
            if len(relocated) == 1:
                private_moves.append(
                    dict(before=d["name"], after=relocated[0]["name"], body_preserved=True)
                )
            else:
                issues["changedPrivateDefinitions"].append(d["name"])
            continue
        if not choices:
            issues["missingPublicDeclarations"].append(d["name"])
            continue
        if not same:
            same = [e for e in choices if approved(d, e)]
            if not same:
                issues["changedStatements"].append(d["name"])
                continue
            approved_changes.add(d["name"])
        e = next((e for e in same if e["file"] == d["file"]), same[0])
        if d["tags"] != e["tags"]:
            issues["changedTags"].append(d["name"])
        if d["kind"] in ["def", "abbrev", "opaque"] and d["body"] != e["body"]:
            issues["changedDefinitions"].append(d["name"])
        if not d["sorry"] and e["sorry"]:
            issues["newAdmissionsInExistingProofs"].append(d["name"])
        if d["file"] != e["file"]:
            moves.append(dict(name=d["name"], before=d["file"], after=e["file"]))
            moved_docs_checked += 1
            old_doc = declaration_docstring(sources[d["file"]], d["line"])
            new_doc = declaration_docstring(current[e["file"]], e["line"])
            if mathematical_docstring(old_doc) != mathematical_docstring(new_doc):
                issues["changedMovedDocstrings"].append(d["name"])
            if (
                old_doc
                and "**Admitted.**" in old_doc
                and new_doc
                and "**Admitted.**" not in new_doc
            ):
                removed_admission_markers.append(d["name"])

    for e in after:
        if e["sorry"] and e["name"] not in old:
            issues["newAdmittedDeclarations"].append(e["name"])
        if e["kind"] == "axiom" and e["name"] not in old:
            issues["newAxioms"].append(e["name"])
    completed = []
    missing = []
    for d in before:
        if not d["sorry"]:
            continue
        choices = [
            e for e in new[d["name"]] if e["head"] == d["head"] or approved(d, e)
        ]
        if not choices:
            missing.append(d["name"])
        elif any(not e["sorry"] for e in choices):
            completed.append(d["name"])
    if missing:
        issues["missingOriginalAdmissions"] = missing
    unused_approvals = sorted(set(approvals) - approved_changes)
    if unused_approvals:
        issues["unusedApprovedCorrections"] = unused_approvals
    new_public = sorted(
        {
            d["name"]
            for d in after
            if not d["private"] and not any(not e["private"] for e in old[d["name"]])
        }
    )
    if args.new_public_names:
        Path(args.new_public_names).write_text("\n".join(new_public) + "\n")
    digest = hashlib.sha256()
    for p, s in sorted(current.items()):
        digest.update((p + "\0" + s + "\0").encode())
    result = dict(
        baseline_commit=args.baseline,
        checked_public_declarations=sum(not d["private"] for d in before),
        baseline_direct_admissions=sum(d["sorry"] for d in before),
        remaining_direct_admissions=sum(d["sorry"] for d in after),
        completed_original_admissions=completed,
        new_public_declarations=len(new_public),
        moved_public_declarations=moves,
        private_definition_relocations=private_moves,
        moved_public_docstrings_checked=moved_docs_checked,
        removed_obsolete_admission_markers=removed_admission_markers,
        approved_statement_corrections=sorted(approved_changes),
        source_digest_sha256=digest.hexdigest(),
        issues=dict(issues),
        status="passed" if not issues else "needs_review",
    )
    Path(args.output).write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(
        json.dumps(
            {
                k: v
                for k, v in result.items()
                if k not in ["completed_original_admissions", "moved_public_declarations"]
            },
            ensure_ascii=False,
        )
    )
    return 0 if not issues else 1


if __name__ == "__main__":
    raise SystemExit(main())
