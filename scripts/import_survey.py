#!/usr/bin/env python3
"""Survey the imports between areas of the DLMF library (AGENTS.md, "Imports within DLMF").

Usage (from the project root):

    python3 scripts/import_survey.py [--baseline scripts/import_baseline.json] [--write-baseline]

The script reads the `import` lines of every module under `DLMF/` (sources only; no build is
needed) and reports

* the number of areas, modules and cross-area import lines;
* the pairs of areas that import each other (two-way pairs), with an example file edge each way;
* the strongly connected components of the area graph (areas that depend on each other);
* all imports from foundational files into theorem files, within or across areas;
* missing project modules and file-import cycles.

An area is the second component of a module name (`DLMF.Bessel.Basic` lies in `Bessel`). An
area umbrella `DLMF/<Area>.lean` (one with a directory `DLMF/<Area>/`) and the
`DLMF.Basic` foundational entry point are ignored in the area graph. A
foundational file is recognised by name: a `Basic` module, any module below a `Basic/`
directory, or a legacy `Defs`/`Definitions` module. Imports of `DLMF.Core.*` modules
(the project framework) are exempt. Both same-area and cross-area foundational imports
are checked; area umbrellas are not foundational modules.

With `--baseline`, two-way pairs and definitions-file imports that are already in the baseline
are listed as known and the new ones are marked NEW. Foundational violations, missing
project modules and file-import cycles always fail; they cannot be grandfathered by a baseline.
`--write-baseline` writes the current state to the baseline file instead.
"""

import argparse
import collections
import json
import os
import re
import sys

IMPORT_RE = re.compile(r'^(?:public\s+)?import\s+(\S+)', re.M)
DEF_NAMES = {'Basic', 'Defs', 'Definitions'}


def read_modules(root):
    """Map each module under `DLMF/` to the list of modules it imports."""
    mods = {}
    for d, _, files in os.walk(os.path.join(root, 'DLMF')):
        for f in files:
            if f.endswith('.lean'):
                path = os.path.join(d, f)
                name = os.path.relpath(path, root)[:-5].replace(os.sep, '.')
                with open(path, encoding='utf8') as h:
                    mods[name] = IMPORT_RE.findall(h.read())
    return mods


def umbrellas(root, mods):
    """The area umbrellas `DLMF.<Area>` that have a directory `DLMF/<Area>/`."""
    return {m for m in mods
            if m.count('.') == 1 and os.path.isdir(os.path.join(root, 'DLMF', m.split('.')[1]))} | ({'DLMF.Basic'} & mods.keys())


def area(m):
    """The area of a module: `DLMF.X.Y…` lies in `X`, a top-level `DLMF.X` is its own area."""
    return m.split('.')[1]


def is_defs(m):
    parts = m.split('.')
    return 'Basic' in parts[2:] or parts[-1] in DEF_NAMES


def survey(root):
    mods = read_modules(root)
    umb = umbrellas(root, mods)
    edges = collections.defaultdict(list)
    defs_imports = []
    for m, imps in sorted(mods.items()):
        for i in imps:
            if (is_defs(m) and i in mods and area(i) != 'Core' and not is_defs(i)):
                defs_imports.append(f'{m} -> {i}')
            if m in umb or m == 'DLMF':
                continue
            if i not in mods or i in umb or area(i) == area(m) or area(i) == 'Core':
                continue
            edges[(area(m), area(i))].append((m, i))
    graph = collections.defaultdict(set)
    for a, b in edges:
        graph[a].add(b)
    two_way = sorted(f'{a} <-> {b}' for (a, b) in edges if (b, a) in edges and a < b)
    return mods, umb, edges, two_way, strongly_connected(graph), defs_imports


def strongly_connected(graph):
    """Tarjan's algorithm; returns the components with more than one area."""
    sys.setrecursionlimit(10000)
    index, low, stack, on, comps, counter = {}, {}, [], set(), [], [0]

    def visit(v):
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        on.add(v)
        for w in sorted(graph[v]):
            if w not in index:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            comp = []
            while True:
                w = stack.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            if len(comp) > 1:
                comps.append(sorted(comp))

    for v in sorted(set(graph) | {w for ws in graph.values() for w in ws}):
        if v not in index:
            visit(v)
    return sorted(comps)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--root', default='.')
    ap.add_argument('--baseline')
    ap.add_argument('--write-baseline', action='store_true')
    args = ap.parse_args()
    mods, umb, edges, two_way, comps, defs_imports = survey(args.root)

    missing = sorted(f'{m} -> {i}' for m, imports in mods.items()
                     for i in imports if i.startswith('DLMF.') and i not in mods)
    module_graph = {m: {i for i in imports if i in mods} for m, imports in mods.items()}
    cycles = strongly_connected(module_graph)
    self_imports = sorted(m for m, imports in mods.items() if m in imports)

    if args.write_baseline:
        if defs_imports or missing or cycles or self_imports:
            ap.error('foundational violations, missing imports and file cycles cannot be baselined')
        if not args.baseline:
            ap.error('--write-baseline needs --baseline FILE')
        with open(args.baseline, 'w', encoding='utf8') as h:
            json.dump({'two_way_pairs': two_way, 'defs_imports': defs_imports}, h, indent=1)
            h.write('\n')
        print(f'wrote {args.baseline}: {len(two_way)} two-way pairs, '
              f'{len(defs_imports)} definitions-file imports')
        return 0

    known = {'two_way_pairs': [], 'defs_imports': []}
    if args.baseline:
        with open(args.baseline, encoding='utf8') as h:
            known = json.load(h)

    n_modules = len(mods) - len(umb) - ('DLMF' in mods)
    n_areas = len({area(m) for m in mods if m not in umb and m != 'DLMF'})
    print(f'{n_areas} areas, {n_modules} modules, '
          f'{sum(len(v) for v in edges.values())} cross-area import lines '
          f'(DLMF.Core excluded), {len(edges)} area edges')
    new = 0
    print(f'\nTwo-way area pairs ({len(two_way)}):')
    for p in two_way:
        a, b = p.split(' <-> ')
        tag = '' if p in known['two_way_pairs'] or not args.baseline else '  NEW'
        new += bool(tag)
        print(f'  {p}{tag}: {edges[(a, b)][0][0]} -> {edges[(a, b)][0][1]}; '
              f'{edges[(b, a)][0][0]} -> {edges[(b, a)][0][1]}')
    print(f'\nStrongly connected groups of areas ({len(comps)}):')
    for c in comps:
        print(f'  {len(c)}: {", ".join(c)}')
    print(f'\nFoundational files importing non-foundational DLMF modules ({len(defs_imports)}):')
    for d in defs_imports:
        tag = '' if d in known['defs_imports'] or not args.baseline else '  NEW'
        new += bool(tag)
        print(f'  {d}{tag}')
    if args.baseline:
        print(f'\n{new} new item(s) relative to {args.baseline}')
    print(f'\nMissing project imports ({len(missing)}):')
    for item in missing:
        print(f'  {item}')
    print(f'\nFile-import cycles ({len(cycles) + len(self_imports)}):')
    for component in cycles:
        print('  ' + ', '.join(component))
    for module in self_imports:
        print(f'  {module} imports itself')
    return 1 if new or defs_imports or missing or cycles or self_imports else 0


if __name__ == '__main__':
    sys.exit(main())
