#!/usr/bin/env python3
"""Regenerate the declaration links and statuses of the DLMF acquisition ledgers.

Usage (from the project root, after `lake build` and scripts/DumpDLMF.lean):

    python3 scripts/dlmf_ledgers.py dlmf-tags.json [--dry] LEDGER.md ...

The tag dump written by scripts/DumpDLMF.lean is the source of truth for every declaration
carrying an `@[dlmf]` attribute: its location and its status from the compiled axiom audit.
Linked declarations without a DLMF tag fall back to a source scan (location, and an explicit
`sorry` in the declaration body for the status). For each ledger the script

* rewrites every link `[name](file.lean#Ln) (status)` to the current file and line, and the
  status to `proved`, `admitted`, or `proved from admissions` (a proof without `sorry` of its
  own that depends on admitted lemmas; known only for tagged declarations), keeping the
  `definition`/`defined` labels;
* appends to each equation line `- [ID](https://dlmf.nist.gov/ID): ...` the project
  declarations tagged `ID` that the line does not yet mention, and Mathlib or TauCeti
  declarations tagged `ID` as upstream pointers;
* inserts a line for each tagged ID of the ledger's chapters that has no line yet, after the
  last line of the same section;
* rewrites the module admission counts (`- [Mod](DLMF/...lean): N admissions.` and the
  `N definitions, M statements, P proved, A admitted.` inventory lines);
* reports links whose declaration is missing, and links whose declaration carries DLMF tags
  none of which is the line's ID.
Prose is never changed.
"""
import collections
import json
import os
import re
import sys

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s(:{\[]+)', re.M)
LINK = re.compile(r'\[(`?)([^\]`]+)`?\]\(([^)#]*\.lean)(?:#L(\d+))?\) '
                  r'\((admitted|proved|proved from admissions|definition|defined|nonstandard axioms)\)')
EQLINE = re.compile(r'^- \[(\d+\.\d+(?:\.(?:[ETF]\d+(?:_\d+)*|[ivx]+))?)\]\(https://dlmf\.nist\.gov/\1\):')


def strip_comments(s):
    s = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), s, flags=re.S)
    return re.sub(r'--[^\n]*', '', s)


def scan_source(roots):
    """Declarations by name (as written) with file, line, kind and explicit-sorry flag."""
    idx = collections.defaultdict(list)
    admitted = collections.Counter()
    stats = {}
    for root in roots:
        for dp, _, fs in os.walk(root):
            for f in fs:
                if not f.endswith('.lean'):
                    continue
                p = os.path.normpath(os.path.join(dp, f))
                s = strip_comments(open(p).read())
                ms = list(DECL.finditer(s))
                nd = nt = 0
                for i, m in enumerate(ms):
                    body = s[m.end(): ms[i + 1].start() if i + 1 < len(ms) else len(s)]
                    sor = bool(re.search(r'\bsorry\b', body))
                    admitted[p] += sor
                    nd += m.group(1) in ('def', 'abbrev')
                    nt += m.group(1) in ('theorem', 'lemma')
                    idx[m.group(2)].append((p, s.count('\n', 0, m.start()) + 1, m.group(1), sor))
                stats[p] = (nd, nt)
    return idx, admitted, stats


def theorem_status(e):
    """Ledger label for the status of a dumped theorem."""
    if e['status'] == 'admitted' and e.get('sorryDirect') is False:
        return 'proved from admissions'
    return {'nonstandard': 'nonstandard axioms'}.get(e['status'], e['status'])


def suffixes(name):
    parts = name.split('.')
    return ['.'.join(parts[i:]) for i in range(len(parts))]


def main():
    args = [a for a in sys.argv[1:] if a != '--dry']
    dry = '--dry' in sys.argv
    dump = json.load(open(args[0]))
    ledgers = args[1:]
    entries = dump['entries']
    by_decl = collections.defaultdict(list)
    by_suffix = collections.defaultdict(list)
    by_id = collections.defaultdict(list)
    for e in entries:
        by_decl[e['decl']].append(e)
        for s in suffixes(e['decl']):
            by_suffix[s].append(e)
        by_id[e['dlmf']].append(e)
    src, admitted, stats = scan_source(['DLMF', 'DLMFMathlib'])

    def resolve(name, path):
        """Dump entry or source record for a linked name, preferring the linked file."""
        for key in suffixes(name):
            cands = by_decl.get(key) or by_suffix.get(key) or []
            cands = list({c['decl']: c for c in cands}.values())
            if cands:
                hit = [c for c in cands if os.path.normpath(c['file']) == path] or cands
                if len(hit) == 1 or len({c['file'] for c in hit}) == 1:
                    return 'dump', hit[0]
            recs = src.get(key)
            if recs:
                hit = [r for r in recs if r[0] == path] or recs
                return 'src', hit[0]
        return None, None

    for ledger in ledgers:
        base = os.path.dirname(ledger)
        rel = lambda p: os.path.relpath(p, base or '.')
        text = open(ledger).read()
        full_names = '`DLMF.' in text
        chapters = {m.split('.')[0] for m in re.findall(r'^- \[(\d+\.\d+\.[^\]]+)\]', text, re.M)}
        stat = collections.Counter()
        report = []

        def label(name):
            if full_names:
                return f'`{name}`'
            parts = name.split('.')
            return '.'.join(parts[2:]) if parts[0] == 'DLMF' and len(parts) > 2 else name

        def deflabel():
            return 'defined' if '(defined)' in text else 'definition'

        def fmt(e):
            st = theorem_status(e) if e['kind'] == 'theorem' else deflabel()
            return f"[{label(e['decl'])}]({rel(e['file'])}#L{e['line']}) ({st})"

        def relink(m, line_id=None):
            bt, name, path, _, status = m.groups()
            path_n = os.path.normpath(os.path.join(base, path))
            kind, rec = resolve(name, path_n)
            if kind is None:
                stat['missing'] += 1
                report.append(f'missing declaration: {name} ({path})')
                return m.group(0), None
            if kind == 'dump':
                file, line, decl = os.path.normpath(rec['file']), rec['line'], rec['decl']
                new = status if status in ('definition', 'defined') else theorem_status(rec)
                stat['from dump'] += 1
                if line_id and line_id not in {e['dlmf'] for e in by_decl[decl]}:
                    report.append(f'{line_id}: {decl} is tagged '
                                  f'{sorted({e["dlmf"] for e in by_decl[decl]})}')
            else:
                file, line, k, sor = rec
                decl = name
                new = status if status in ('definition', 'defined') else ('admitted' if sor else 'proved')
                stat['from source'] += 1
            if new != status:
                stat[f'{status} -> {new}'] += 1
            if os.path.normpath(file) != path_n:
                stat['moved'] += 1
            return f'[{bt}{name}{bt}]({rel(file)}#L{line}) ({new})', decl

        out = []
        seen_ids = set()
        # Lines sharing an ID: what any of them mentions counts for all, and missing
        # declarations are appended to the last of them only.
        lines_in = text.split('\n')
        id_text = collections.defaultdict(str)
        last_line = {}
        for k, l in enumerate(lines_in):
            em0 = EQLINE.match(l)
            if em0:
                id_text[em0.group(1)] += l + '\n'
                last_line[em0.group(1)] = k
        for k, line in enumerate(lines_in):
            em = EQLINE.match(line)
            if not em:
                out.append(LINK.sub(lambda m: relink(m)[0], line))
                continue
            lid = em.group(1)
            seen_ids.add(lid)
            linked = set()

            def rep(m):
                s, decl = relink(m, lid)
                if decl:
                    linked.add(decl)
                return s
            line = LINK.sub(rep, line)
            if last_line[lid] != k:
                out.append(line)
                continue
            all_text = id_text[lid]
            for m in LINK.finditer(all_text):
                linked.add(m.group(2))
            linked_suffix = {s for d in linked for s in suffixes(d)}
            extra = []
            for e in by_id.get(lid, []):
                if (e['decl'] in linked or e['decl'] in linked_suffix
                        or label(e['decl']).strip('`') in all_text):
                    continue
                if e['project'] == 'lean-DLMF':
                    extra.append(fmt(e))
                    stat['appended'] += 1
                elif e['docUrl'] or e['sourceUrl']:
                    if e['decl'] in all_text:
                        continue
                    extra.append(f"{e['project']}: [`{e['decl']}`]({e['docUrl'] or e['sourceUrl']})")
                    stat['upstream pointers'] += 1
            if extra:
                body = line[:-1] if line.endswith('.') else line
                line = body + '; ' + '; '.join(extra) + '.'
            out.append(line)

        # Tagged IDs of this ledger's chapters that have no line yet.
        missing_ids = sorted({i for i in by_id if i.split('.')[0] in chapters and i not in seen_ids
                              and any(e['project'] == 'lean-DLMF' for e in by_id[i])},
                             key=lambda i: [int(x) if x.isdigit() else x
                                            for x in re.split(r'[.ETF]', i) if x])
        for lid in missing_ids:
            sec = '.'.join(lid.split('.')[:2]) + '.'
            pos = max((k for k, l in enumerate(out) if l.startswith(f'- [{sec}')), default=None)
            if pos is None:
                report.append(f'no section for new ID {lid}')
                continue
            items = '; '.join(fmt(e) for e in by_id[lid] if e['project'] == 'lean-DLMF')
            out.insert(pos + 1, f'- [{lid}](https://dlmf.nist.gov/{lid}): {items}.')
            stat['new lines'] += 1
        text = '\n'.join(out)

        # Module counts.
        def r1(m):
            p = os.path.normpath(os.path.join(base, m.group(2)))
            return m.group(0) if p not in stats else f'- [{m.group(1)}]({m.group(2)}): {admitted[p]} admissions.'
        text = re.sub(r'^- \[(\w+)\]\(([^)]+\.lean)\): \d+ admissions\.', r1, text, flags=re.M)

        def r2(m):
            p = os.path.normpath(os.path.join(base, m.group(2)))
            if p not in stats:
                return m.group(0)
            d, n = stats[p]
            a = admitted[p]
            return f'- [{m.group(1)}]({m.group(2)}): {d} definitions, {n} statements, {n - a} proved, {a} admitted.'
        text = re.sub(r'^- \[([^\]]+\.lean)\]\(([^)]+\.lean)\): \d+ definitions, \d+ statements, '
                      r'\d+ proved, \d+ admitted\.', r2, text, flags=re.M)

        print(f'{ledger}: {dict(stat)}')
        for r in report:
            print('  ' + r)
        if not dry:
            open(ledger, 'w').write(text)


if __name__ == '__main__':
    main()
