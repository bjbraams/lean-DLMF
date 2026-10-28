#!/usr/bin/env python3
"""Enforce the project's 1500-line limit on Lean source files."""
from pathlib import Path

LIMIT = 1500
ROOT = Path(__file__).resolve().parents[1]


def main() -> int:
    sources = sorted(
        path for path in ROOT.rglob('*.lean')
        if '.lake' not in path.relative_to(ROOT).parts
        and '.git' not in path.relative_to(ROOT).parts
    )
    oversized = []
    for path in sources:
        count = len(path.read_text(encoding='utf-8').splitlines())
        if count > LIMIT:
            oversized.append((path.relative_to(ROOT), count))
    for path, count in oversized:
        print(f'{path}: {count} lines (limit {LIMIT})')
    if oversized:
        return 1
    print(f'All {len(sources)} Lean source files are at most {LIMIT} lines.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
