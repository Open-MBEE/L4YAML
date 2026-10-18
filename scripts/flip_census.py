#!/usr/bin/env python3
"""Resolve Lean build errors to the enclosing declaration — the unit that prices a flip.

A flip patch (`flip_210.py`, `flip_drop.py`, `flip_beta5.py`, the 5a(iv) alias-guard
flip) is priced by the DISTINCT DECLARATIONS it breaks, not by error sites: one lemma
can log four errors and is still one proof to repair.  This resolves each error to its
declaration, and separates gate sites (`#guard`, `#eval`, `#guard_msgs`) from proofs,
because a gate is a decision to re-take rather than a proof to repair.

**A single run reports a FLOOR, never the price.**  A failing module blocks its
dependents, so the next layer never elaborates.  To get the whole bill, sorry the
round's breakages, rebuild, and re-run; repeat until a round adds nothing but `sorryAx`
artifacts.  Measured 2026-10-03: round 1 said 6 declarations, the descent said 10.

Usage:  python3 scripts/flip_census.py BUILD.log [REPO_ROOT]

The number that prices a flip is DISTINCT DECLARATIONS BROKEN, not error
sites: one lemma can log four errors and is still one proof to repair.
Reads a build log on stdin or as argv[1]; resolves each `file:line:col: error:`
against the file on disk by scanning backwards for the nearest declaration opener
at column 0.
"""
import re
import sys
import pathlib
from collections import OrderedDict

# A `#guard` / `#eval` / `#guard_msgs` failure is a GATE site, not a broken
# declaration: it has no name, and scanning backwards for the nearest opener
# silently bills it to whatever `def` happens to precede it.  (Measured
# 2026-10-18: three `#guard`s in `Serialization/Census.lean` were all reported
# as `def tagCases`.)  They are counted as their own class.
COMMAND = re.compile(r'^\s*(#guard_msgs|#guard|#eval|#check|#print|#reduce)\b')

OPENER = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|partial\s+|noncomputable\s+|unsafe\s+|public\s+)*'
    r'(theorem|lemma|def|instance|abbrev|example|structure|inductive|class)\b'
    r'(?:\s+([A-Za-z_α-ω][^\s:({\[]*))?'
)
# Lean/lake print the location on either side of the severity, depending on
# version and on whether lake is quoting a worker's message.  Accept both:
#   error: file.lean:LINE:COL: MESSAGE
#   file.lean:LINE:COL: error: MESSAGE
ERR = re.compile(
    r'^(?:error: (?P<f1>\S+\.lean):(?P<l1>\d+):(?P<c1>\d+): (?P<m1>.*)'
    r'|(?P<f2>\S+\.lean):(?P<l2>\d+):(?P<c2>\d+): error: (?P<m2>.*))$'
)


def enclosing(path: pathlib.Path, lineno: int):
    try:
        lines = path.read_text().splitlines()
    except OSError:
        return None, None
    # A command at (or immediately above) the error line owns the site.
    for i in range(min(lineno, len(lines)) - 1, max(min(lineno, len(lines)) - 3, -1), -1):
        m = COMMAND.match(lines[i])
        if m:
            return m.group(1), f'<{pathlib.Path(path).name}:{i + 1}>'
    for i in range(min(lineno, len(lines)) - 1, -1, -1):
        m = OPENER.match(lines[i])
        if m:
            return m.group(1), (m.group(2) or '<anonymous>')
    return None, None


def main():
    log = pathlib.Path(sys.argv[1]).read_text() if len(sys.argv) > 1 else sys.stdin.read()
    root = pathlib.Path(sys.argv[2] if len(sys.argv) > 2 else '.')

    sites = []
    for raw in log.splitlines():
        m = ERR.match(raw.strip())
        if not m:
            continue
        g = m.groupdict()
        rel = g['f1'] or g['f2']
        line = int(g['l1'] or g['l2'])
        msg = g['m1'] if g['m1'] is not None else g['m2']
        kind, name = enclosing(root / rel, line)
        sites.append((rel, line, kind, name, msg[:40]))

    print(f"=== {len(sites)} error sites, resolved to the enclosing declaration ===")
    for rel, line, kind, name, msg in sites:
        shown = f"{kind} {name}" if kind else "<no enclosing declaration>"
        print(f"  {rel}:{line}  {shown}   [{msg}]")

    # DISTINCT declarations: keyed by (file, name), because the twins share names.
    distinct = OrderedDict()
    for rel, line, kind, name, _msg in sites:
        if kind is None:
            continue
        distinct.setdefault((rel, kind, name), []).append(line)

    print()
    print(f"=== {len(distinct)} DISTINCT declarations broken "
          f"(the number that prices the work) ===")
    for (rel, kind, name), lines in distinct.items():
        print(f"  {kind} {name}  ({pathlib.Path(rel).name}, lines {sorted(set(lines))})")

    files = sorted({pathlib.Path(rel).name for (rel, _k, _n) in distinct})
    cmds = {k: v for k, v in distinct.items() if COMMAND.match('#' + k[1].lstrip('#'))}
    decls = {k: v for k, v in distinct.items() if k not in cmds}
    print()
    print(f"files: {len(files)}  {files}")
    print(f"TALLY declarations={len(decls)} gate-sites={len(cmds)} "
          f"sites={len(sites)} files={len(files)}")
    if cmds:
        print("  gate sites are NOT declarations to repair; they are pins to re-decide:")
        for (rel, kind, name), lns in cmds.items():
            print(f"    {kind} {name}  ({pathlib.Path(rel).name})")


if __name__ == '__main__':
    main()
